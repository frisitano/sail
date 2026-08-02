open Ast
open Ast_util
open Jib
open Type_check

module InstructionSet = Set.Make (Int)
module InstructionMap = Map.Make (Int)

type operation = Add | Subtract | Multiply

type reduction = Truncating | Euclidean

type observation = Exact | Low_bits of int | Checked | Saturating

type comparison = Equal | Not_equal | Less_than | Less_equal | Greater_than | Greater_equal

type identity = { owner : id; instruction : int }

type fact = { logical_type : ctyp; interval : integer_interval option; unsigned : bool }

type evidence = {
  identity : identity;
  operation : operation;
  reduction : reduction;
  observation : observation;
  modulus : Nat_big_num.num;
  operands : fact list;
  proofs : semantic_proof list;
  dependencies : InstructionSet.t;
}

type t = evidence InstructionMap.t

let empty = InstructionMap.empty
let record evidence = InstructionMap.add evidence.identity.instruction evidence
let find ~instruction evidence = InstructionMap.find_opt instruction evidence

let invalidate_missing present =
  InstructionMap.filter (fun _ evidence -> InstructionSet.subset evidence.dependencies present)

let bindings evidence = List.map snd (InstructionMap.bindings evidence)

let fixed_unsigned_bounds width =
  if width < 0 then None
  else Some (Big_int.zero, Big_int.pred (Big_int.pow_int_positive 2 width))

let rec refine_comparison_bounds comparison ~truth ~left:(left_lower, left_upper) ~right:(right_lower, right_upper) =
  let interval lower upper = if Big_int.less_equal lower upper then Some (lower, upper) else None in
  let intersect (left_lower, left_upper) (right_lower, right_upper) =
    interval (Big_int.max left_lower right_lower) (Big_int.min left_upper right_upper)
  in
  let exclude value (lower, upper) =
    if Big_int.less value lower || Big_int.greater value upper then Some (lower, upper)
    else if Big_int.equal lower upper then None
    else if Big_int.equal value lower then Some (Big_int.succ lower, upper)
    else if Big_int.equal value upper then Some (lower, Big_int.pred upper)
    else Some (lower, upper)
  in
  let equal () =
    Option.map (fun bounds -> (bounds, bounds))
      (intersect (left_lower, left_upper) (right_lower, right_upper))
  in
  let not_equal () =
    if Big_int.equal left_lower left_upper then
      Option.map (fun right -> ((left_lower, left_upper), right))
        (exclude left_lower (right_lower, right_upper))
    else if Big_int.equal right_lower right_upper then
      Option.map (fun left -> (left, (right_lower, right_upper)))
        (exclude right_lower (left_lower, left_upper))
    else Some ((left_lower, left_upper), (right_lower, right_upper))
  in
  let less_than () =
    Option.bind (interval left_lower (Big_int.min left_upper (Big_int.pred right_upper))) (fun left ->
        Option.map
          (fun right -> (left, right))
          (interval (Big_int.max right_lower (Big_int.succ left_lower)) right_upper)
    )
  in
  let less_equal () =
    Option.bind (interval left_lower (Big_int.min left_upper right_upper)) (fun left ->
        Option.map
          (fun right -> (left, right))
          (interval (Big_int.max right_lower left_lower) right_upper)
    )
  in
  match (comparison, truth) with
  | Equal, true | Not_equal, false -> equal ()
  | Equal, false | Not_equal, true -> not_equal ()
  | Less_than, true | Greater_equal, false -> less_than ()
  | Less_equal, true | Greater_than, false -> less_equal ()
  | Greater_than, true | Less_equal, false ->
      Option.map (fun (right, left) -> (left, right))
        (refine_comparison_bounds Less_than ~truth:true ~left:(right_lower, right_upper)
           ~right:(left_lower, left_upper)
        )
  | Greater_equal, true | Less_than, false ->
      Option.map (fun (right, left) -> (left, right))
        (refine_comparison_bounds Less_equal ~truth:true ~left:(right_lower, right_upper)
           ~right:(left_lower, left_upper)
        )

let nonnegative_upper = function
  | Some (lower, upper) when Big_int.less_equal Big_int.zero lower -> Some upper
  | Some _ | None -> None

let unsigned_width value =
  if Big_int.less value Big_int.zero then None
  else (
    let rec width bits value =
      if Big_int.equal value Big_int.zero then bits else width (bits + 1) (Big_int.shift_right value 1)
    in
    Some (width 0 value)
  )

let prove_low_mask_width ~carrier_width ~mask =
  if carrier_width <= 0 || Big_int.less_equal mask Big_int.zero then None
  else
    Option.bind (unsigned_width mask) (fun width ->
        match fixed_unsigned_bounds width with
        | Some (_, expected) when width <= carrier_width && Big_int.equal mask expected -> Some width
        | Some _ | None -> None
    )

let unsigned_cover upper = Option.bind (unsigned_width upper) (fun width -> fixed_unsigned_bounds width)

let slice_result_bounds ~width ~source ~start =
  match (fixed_unsigned_bounds width, nonnegative_upper source, start) with
  | Some (_, width_upper), Some source_upper, Some (start_lower, _)
    when Big_int.less_equal Big_int.zero start_lower ->
      let shifted_upper =
        match unsigned_width source_upper with
        | Some source_width when Big_int.greater_equal start_lower (Big_int.of_int source_width) -> Big_int.zero
        | Some _ when Big_int.less_equal start_lower (Big_int.of_int Stdlib.max_int) ->
            Big_int.shift_right source_upper (Big_int.to_int start_lower)
        | Some _ | None -> Big_int.zero
      in
      Some (Big_int.zero, Big_int.min width_upper shifted_upper)
  | Some bounds, _, _ -> Some bounds
  | None, _, _ -> None

let concat_result_bounds ~right_width ~left ~right =
  match (nonnegative_upper left, nonnegative_upper right, fixed_unsigned_bounds right_width) with
  | Some left_upper, Some right_upper, Some (_, right_width_upper) ->
      let shifted_left = Big_int.mul left_upper (Big_int.pow_int_positive 2 right_width) in
      Some (Big_int.zero, Big_int.add shifted_left (Big_int.min right_upper right_width_upper))
  | (Some _, Some _, None) | (None, _, _) | (_, None, _) -> None

let bitwise_and_result_bounds ~left ~right =
  match (nonnegative_upper left, nonnegative_upper right) with
  | Some left_upper, Some right_upper -> Some (Big_int.zero, Big_int.min left_upper right_upper)
  | None, _ | _, None -> None

let bitwise_union_result_bounds ~left ~right =
  match (nonnegative_upper left, nonnegative_upper right) with
  | Some left_upper, Some right_upper -> unsigned_cover (Big_int.max left_upper right_upper)
  | None, _ | _, None -> None

let bit_insert_result_bounds ~carrier_width ~base ~start ~inserted =
  match (fixed_unsigned_bounds carrier_width, nonnegative_upper base, start, nonnegative_upper inserted) with
  | Some (_, carrier_upper), Some base_upper, Some (start_lower, start_upper), Some inserted_upper
    when Big_int.less_equal Big_int.zero start_lower -> (
      match (unsigned_width base_upper, unsigned_width inserted_upper) with
      | Some base_width, Some inserted_width ->
          let occupied_width =
            if Big_int.greater start_upper (Big_int.of_int carrier_width) then carrier_width
            else
              let start_upper = Big_int.to_int start_upper in
              if inserted_width >= carrier_width - start_upper then carrier_width else start_upper + inserted_width
          in
          let result_width = min carrier_width (max base_width occupied_width) in
          Option.map
            (fun (_, upper) -> (Big_int.zero, Big_int.min carrier_upper upper))
            (fixed_unsigned_bounds result_width)
      | None, _ | _, None -> None
    )
  | Some bounds, _, _, _ -> Some bounds
  | None, _, _, _ -> None

let interval_proves_argument_le left right =
  match (left, right) with
  | Some (_, left_upper), Some (right_lower, _) -> Big_int.less_equal left_upper right_lower
  | _ -> false

let symbolic_range env typ =
  match Type_check.destruct_range env typ with
  | Some (kids, constr, lower, upper) ->
      let env = Type_check.add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr env in
      Some (env, lower, upper)
  | None -> None

let prove_argument_le ~env ~left_index ~left_typ ~left_interval ~right_index ~right_typ ~right_interval =
  let proof semantic_proof_method =
    Some { semantic_relation = Argument_le (left_index, right_index); semantic_proof_method }
  in
  if interval_proves_argument_le left_interval right_interval then proof Proof_interval
  else (
    match symbolic_range env left_typ with
    | None -> None
    | Some (env, _, left_upper) -> (
        match symbolic_range env right_typ with
        | Some (env, right_lower, _) when Type_check.prove __POS__ env (nc_lteq left_upper right_lower) ->
            proof Proof_type_constraint
        | Some _ | None -> None
      )
  )

let prove_result_nonnegative ~env ~result_typ ~result_interval =
  let proof semantic_proof_method = Some { semantic_relation = Result_nonnegative; semantic_proof_method } in
  match result_interval with
  | Some (lower, _) when Big_int.greater_equal lower Big_int.zero -> proof Proof_interval
  | Some _ | None -> (
      match symbolic_range env result_typ with
      | Some (env, lower, _) when Type_check.prove __POS__ env (nc_lteq (nint 0) lower) -> proof Proof_type_constraint
      | Some _ | None -> None
    )

let prove_argument_bounds ~env ~index ~typ ~interval ~lower ~upper =
  let proof semantic_proof_method =
    Some { semantic_relation = Argument_bounds (index, lower, upper); semantic_proof_method }
  in
  match interval with
  | Some (actual_lower, actual_upper)
    when Big_int.less_equal lower actual_lower && Big_int.less_equal actual_upper upper ->
      proof Proof_interval
  | Some _ | None -> (
      match symbolic_range env typ with
      | Some (env, actual_lower, actual_upper)
        when Type_check.prove __POS__ env (nc_lteq (nconstant lower) actual_lower)
             && Type_check.prove __POS__ env (nc_lteq actual_upper (nconstant upper)) ->
          proof Proof_type_constraint
      | Some _ | None -> None
    )

let prove_result_bounds ~env ~result_typ ~result_interval ~lower ~upper =
  let proof semantic_proof_method = Some { semantic_relation = Result_bounds (lower, upper); semantic_proof_method } in
  match result_interval with
  | Some (actual_lower, actual_upper)
    when Big_int.less_equal lower actual_lower && Big_int.less_equal actual_upper upper ->
      proof Proof_interval
  | Some _ | None -> (
      match symbolic_range env result_typ with
      | Some (env, actual_lower, actual_upper)
        when Type_check.prove __POS__ env (nc_lteq (nconstant lower) actual_lower)
             && Type_check.prove __POS__ env (nc_lteq actual_upper (nconstant upper)) ->
          proof Proof_type_constraint
      | Some _ | None -> None
    )

let prove_conversion_value_preserving ~source_width ~target_width =
  if 0 <= source_width && source_width <= target_width then
    Some
      {
        semantic_relation = Conversion_value_preserving (source_width, target_width);
        semantic_proof_method = Proof_structural;
      }
  else None

let prove_signed_conversion_value_preserving ~source_width ~target_width =
  if 0 < source_width && source_width <= target_width then
    Some
      {
        semantic_relation = Signed_conversion_value_preserving (source_width, target_width);
        semantic_proof_method = Proof_structural;
      }
  else None

let prove_conversion_low_bits ~source_width ~target_width =
  if 0 <= target_width && target_width <= source_width then
    Some
      { semantic_relation = Conversion_low_bits (source_width, target_width); semantic_proof_method = Proof_structural }
  else None

let prove_shift_count_interval ~index ~interval ~carrier_width =
  if carrier_width <= 0 then None
  else
    let lower = Big_int.zero in
    let upper = Big_int.of_int (carrier_width - 1) in
    match interval with
    | Some (actual_lower, actual_upper)
      when Big_int.less_equal lower actual_lower && Big_int.less_equal actual_upper upper ->
        Some
          {
            semantic_relation = Shift_count_bounds (index, lower, upper);
            semantic_proof_method = Proof_interval;
          }
    | Some _ | None -> None

let prove_shift_count_bounds ~env ~index ~typ ~interval ~carrier_width =
  match prove_shift_count_interval ~index ~interval ~carrier_width with
  | Some proof -> Some proof
  | None when carrier_width <= 0 -> None
  | None ->
      let lower = Big_int.zero in
      let upper = Big_int.of_int (carrier_width - 1) in
      Option.map
        (fun proof -> { proof with semantic_relation = Shift_count_bounds (index, lower, upper) })
        (prove_argument_bounds ~env ~index ~typ ~interval:None ~lower ~upper)

let prove_bit_insert_position_bounds ~env ~index ~typ ~interval ~carrier_width ~inserted_width =
  if carrier_width < 0 || inserted_width < 0 || inserted_width > carrier_width then None
  else
    prove_argument_bounds ~env ~index ~typ ~interval ~lower:Big_int.zero
      ~upper:(Big_int.of_int (carrier_width - inserted_width))

let has_argument_le ~left ~right proofs =
  List.exists
    (fun proof ->
      match proof.semantic_relation with
      | Argument_le (proof_left, proof_right) -> proof_left = left && proof_right = right
      | Argument_bounds _ | Result_bounds _ | Result_nonnegative | Conversion_value_preserving _
      | Signed_conversion_value_preserving _ | Conversion_low_bits _ | Shift_count_bounds _ ->
          false
    )
    proofs

let has_argument_bounds ~index ~lower ~upper proofs =
  List.exists
    (fun proof ->
      match proof.semantic_relation with
      | Argument_bounds (proof_index, proof_lower, proof_upper) ->
          proof_index = index && Big_int.less_equal lower proof_lower && Big_int.less_equal proof_upper upper
      | Argument_le _ | Result_bounds _ | Result_nonnegative | Conversion_value_preserving _
      | Signed_conversion_value_preserving _ | Conversion_low_bits _ | Shift_count_bounds _ ->
          false
    )
    proofs

let has_result_bounds ~lower ~upper proofs =
  List.exists
    (fun proof ->
      match proof.semantic_relation with
      | Result_bounds (proof_lower, proof_upper) ->
          Big_int.less_equal lower proof_lower && Big_int.less_equal proof_upper upper
      | Argument_le _ | Argument_bounds _ | Result_nonnegative | Conversion_value_preserving _
      | Signed_conversion_value_preserving _ | Conversion_low_bits _ | Shift_count_bounds _ ->
          false
    )
    proofs

let has_result_nonnegative proofs =
  List.exists
    (fun proof ->
      match proof.semantic_relation with
      | Result_nonnegative -> true
      | Argument_le _ | Argument_bounds _ | Result_bounds _ | Conversion_value_preserving _
      | Signed_conversion_value_preserving _ | Conversion_low_bits _ | Shift_count_bounds _ ->
          false
    )
    proofs

let has_conversion_value_preserving ~source_width ~target_width proofs =
  List.exists
    (fun proof ->
      match proof.semantic_relation with
      | Conversion_value_preserving (proof_source, proof_target) ->
          proof_source = source_width && proof_target = target_width
      | Argument_le _ | Argument_bounds _ | Result_bounds _ | Result_nonnegative | Signed_conversion_value_preserving _
      | Conversion_low_bits _ | Shift_count_bounds _ ->
          false
    )
    proofs

let has_signed_conversion_value_preserving ~source_width ~target_width proofs =
  List.exists
    (fun proof ->
      match proof.semantic_relation with
      | Signed_conversion_value_preserving (proof_source, proof_target) ->
          proof_source = source_width && proof_target = target_width
      | Argument_le _ | Argument_bounds _ | Result_bounds _ | Result_nonnegative | Conversion_value_preserving _
      | Conversion_low_bits _ | Shift_count_bounds _ ->
          false
    )
    proofs

let has_conversion_low_bits ~source_width ~target_width proofs =
  List.exists
    (fun proof ->
      match proof.semantic_relation with
      | Conversion_low_bits (proof_source, proof_target) -> proof_source = source_width && proof_target = target_width
      | Argument_le _ | Argument_bounds _ | Result_bounds _ | Result_nonnegative | Conversion_value_preserving _
      | Signed_conversion_value_preserving _ | Shift_count_bounds _ ->
          false
    )
    proofs

let has_shift_count_bounds ~index ~carrier_width proofs =
  let lower = Big_int.zero in
  let upper = Big_int.of_int (carrier_width - 1) in
  List.exists
    (fun proof ->
      match proof.semantic_relation with
      | Shift_count_bounds (proof_index, proof_lower, proof_upper) ->
          proof_index = index && Big_int.less_equal lower proof_lower && Big_int.less_equal proof_upper upper
      | Argument_le _ | Argument_bounds _ | Result_bounds _ | Result_nonnegative | Conversion_value_preserving _
      | Signed_conversion_value_preserving _ | Conversion_low_bits _ ->
          false
    )
    proofs
