(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Ast
open Ast_compare
open Ast_defs
open Ast_util

let opt_readability = ref false

let readability_warning rule l message =
  if not (is_gen_loc l) then Reporting.warn ("Readability lint [" ^ rule ^ "]") l message

let rec strip_typ = function E_aux ((E_typ (_, exp) | E_block [exp]), _) -> strip_typ exp | exp -> exp

let bool_literal exp =
  match strip_typ exp with
  | E_aux (E_lit (L_aux (L_true, _)), _) -> Some true
  | E_aux (E_lit (L_aux (L_false, _)), _) -> Some false
  | _ -> None

let is_unit_literal exp = match strip_typ exp with E_aux (E_lit (L_aux (L_unit, _)), _) -> true | _ -> false

let erase_exp_annotations exp =
  exp |> map_exp_annot (fun _ -> (Parse_ast.Unknown, empty_uannot)) |> locate (fun _ -> Parse_ast.Unknown)

let expressions_equal lhs rhs = Stdlib.compare (erase_exp_annotations lhs) (erase_exp_annotations rhs) = 0

let simple_assignment exp =
  match strip_typ exp with
  | E_aux (E_assign (LE_aux ((LE_id id | LE_typ (_, id)), _), value), _) -> Some (id, value)
  | _ -> None

let is_app named id = String.equal (string_of_id id) named

let parse_id_is_named = function Parse_ast.Id_aux (Parse_ast.Id _, _) -> true | _ -> false

let string_of_parse_id (Parse_ast.Id_aux (aux, _)) =
  match aux with Parse_ast.Id name | Parse_ast.Operator name -> name

let rec strip_parse_exp = function
  | Parse_ast.E_aux ((Parse_ast.E_typ (_, exp) | Parse_ast.E_attribute (_, exp) | Parse_ast.E_block [exp]), _) ->
      strip_parse_exp exp
  | exp -> exp

let parse_bool_literal exp =
  match strip_parse_exp exp with
  | Parse_ast.E_aux (Parse_ast.E_lit (Parse_ast.L_aux (Parse_ast.L_true, _)), _) -> Some true
  | Parse_ast.E_aux (Parse_ast.E_lit (Parse_ast.L_aux (Parse_ast.L_false, _)), _) -> Some false
  | _ -> None

let rec parse_expression_terminates exp =
  let open Parse_ast in
  match strip_parse_exp exp with
  | E_aux ((E_exit _ | E_throw _ | E_return _ | E_internal_return _), _) -> true
  | E_aux (E_block expressions, _) -> (
      match List.rev expressions with last :: _ -> parse_expression_terminates last | [] -> false
    )
  | E_aux ((E_let (_, _, body) | E_internal_plet (_, _, body)), _) -> parse_expression_terminates body
  | E_aux (E_if (_, then_exp, else_exp, _), _) ->
      parse_expression_terminates then_exp && parse_expression_terminates else_exp
  | _ -> false

let rec parse_redundant_nested_if = function
  | Parse_ast.E_aux (Parse_ast.E_block [inner], _) -> (
      match strip_parse_exp inner with Parse_ast.E_aux (Parse_ast.E_if _, _) -> true | _ -> false
    )
  | Parse_ast.E_aux ((Parse_ast.E_typ (_, exp) | Parse_ast.E_attribute (_, exp)), _) -> parse_redundant_nested_if exp
  | _ -> false

let parse_is_unit_literal exp =
  match strip_parse_exp exp with
  | Parse_ast.E_aux (Parse_ast.E_lit (Parse_ast.L_aux (Parse_ast.L_unit, _)), _) -> true
  | _ -> false

let warn_parse_tail_conditional exp =
  let open Parse_ast in
  match strip_parse_exp exp with
  | E_aux (E_if (_, then_exp, else_exp, locations), l)
    when Option.is_some locations.else_loc && Bool.(parse_is_unit_literal then_exp <> parse_is_unit_literal else_exp) ->
      readability_warning "sail-prefer-early-return" l
        "This tail conditional has one empty branch; return from that branch and continue with the non-empty branch as \
         a guard clause."
  | _ -> ()

let rec inspect_parse_tail_exp exp =
  let open Parse_ast in
  warn_parse_tail_conditional exp;
  match strip_parse_exp exp with
  | E_aux (E_block expressions, _) -> (
      match List.rev expressions with last :: _ -> inspect_parse_tail_exp last | [] -> ()
    )
  | E_aux ((E_let (_, _, body) | E_internal_plet (_, _, body) | E_internal_assume (_, body)), _) ->
      inspect_parse_tail_exp body
  | E_aux (E_var (_, _, body), _) -> inspect_parse_tail_exp body
  | E_aux (E_if (_, then_exp, else_exp, _), _) ->
      inspect_parse_tail_exp then_exp;
      inspect_parse_tail_exp else_exp
  | E_aux ((E_match (_, cases) | E_try (_, cases)), _) -> List.iter inspect_parse_tail_pexp cases
  | _ -> ()

and inspect_parse_tail_pexp (Parse_ast.Pat_aux (aux, _)) =
  let open Parse_ast in
  match aux with
  | Pat_exp (_, exp) | Pat_when (_, _, exp) -> inspect_parse_tail_exp exp
  | Pat_attribute (_, pexp) -> inspect_parse_tail_pexp pexp

let rec parse_exp_children (Parse_ast.E_aux (aux, _)) =
  let open Parse_ast in
  match aux with
  | E_block expressions
  | E_app (_, expressions)
  | E_tuple expressions
  | E_vector expressions
  | E_list expressions
  | E_struct (_, expressions) ->
      expressions
  | E_deref exp
  | E_typ (_, exp)
  | E_field (exp, _)
  | E_exit exp
  | E_throw exp
  | E_return exp
  | E_attribute (_, exp)
  | E_internal_return exp
  | E_internal_assume (_, exp) ->
      [exp]
  | E_app_infix (lhs, _, rhs)
  | E_vector_access (lhs, rhs)
  | E_vector_append (lhs, rhs)
  | E_cons (lhs, rhs)
  | E_assign (lhs, rhs)
  | E_assert (lhs, rhs) ->
      [lhs; rhs]
  | E_infix tokens ->
      List.filter_map (function IT_primary exp, _, _ -> Some exp | (IT_op _ | IT_prefix _), _, _ -> None) tokens
  | E_if (condition, then_exp, else_exp, _) -> [condition; then_exp; else_exp]
  | E_loop (_, Measure_aux (measure, _), condition, body) -> (
      match measure with Measure_none -> [condition; body] | Measure_some exp -> [exp; condition; body]
    )
  | E_for (_, from_exp, to_exp, step_exp, _, body) -> [from_exp; to_exp; step_exp; body]
  | E_vector_subrange (vector, high, low) | E_vector_update (vector, high, low) -> [vector; high; low]
  | E_vector_update_subrange (vector, high, low, value) -> [vector; high; low; value]
  | E_struct_update (record, fields) -> record :: fields
  | E_match (subject, cases) | E_try (subject, cases) -> subject :: List.concat_map parse_pexp_expressions cases
  | E_let (_, binding, body) | E_internal_plet (_, binding, body) -> [binding; body]
  | E_var (lexp, binding, body) -> [lexp; binding; body]
  | E_id _ | E_ref _ | E_lit _ | E_sizeof _ | E_constraint _ | E_config _ | E_undef -> []

and parse_pexp_expressions (Parse_ast.Pat_aux (aux, _)) =
  let open Parse_ast in
  match aux with
  | Pat_exp (_, exp) -> [exp]
  | Pat_when (_, guard, exp) -> [guard; exp]
  | Pat_attribute (_, pexp) -> parse_pexp_expressions pexp

let rec parse_named_applications (Parse_ast.E_aux (aux, l) as exp) =
  let nested = List.concat_map parse_named_applications (parse_exp_children exp) in
  match aux with
  | Parse_ast.E_app (id, _) when (not (is_gen_loc l)) && parse_id_is_named id -> string_of_parse_id id :: nested
  | _ -> nested

let rec parse_condition_applications (Parse_ast.E_aux (aux, l) as exp) =
  let nested = List.concat_map parse_condition_applications (parse_exp_children exp) in
  match aux with
  | Parse_ast.E_app (id, _) when (not (is_gen_loc l)) && parse_id_is_named id ->
      let name = string_of_parse_id id in
      if String.equal name "not_bool" then nested else name :: nested
  | _ -> nested

let warn_parse_condition condition =
  match parse_condition_applications condition with
  | [] -> ()
  | calls ->
      let (Parse_ast.E_aux (_, l)) = condition in
      readability_warning "sail-function-call-condition" l
        ("Bind function-call results to named variables before using them in a conditional expression (calls: "
       ^ String.concat ", " calls ^ ")."
        )

let rec inspect_parse_exp (Parse_ast.E_aux (aux, _) as exp) =
  let open Parse_ast in
  ( match aux with
  | E_app (id, arguments) when parse_id_is_named id ->
      List.iter
        (fun argument ->
          match parse_named_applications argument with
          | [] -> ()
          | calls ->
              let (E_aux (_, l)) = argument in
              readability_warning "sail-nested-function-call" l
                ("Bind function-call results to named variables before passing them to another function (nested: "
               ^ String.concat ", " calls ^ ")."
                )
        )
        arguments
  | E_if (condition, then_exp, else_exp, locations) ->
      warn_parse_condition condition;
      if Option.is_some (parse_bool_literal condition) then (
        let (E_aux (_, l)) = exp in
        readability_warning "sail-constant-conditional" l
          "This conditional has a constant condition; retain only the selected branch."
      );
      ( match (parse_bool_literal then_exp, parse_bool_literal else_exp) with
      | Some true, Some false | Some false, Some true ->
          let (E_aux (_, l)) = exp in
          readability_warning "sail-identity-conditional" l
            "This conditional is the condition itself (or its negation)."
      | _ -> ()
      );
      if Option.is_some locations.else_loc && parse_expression_terminates then_exp then (
        let (E_aux (_, l)) = exp in
        readability_warning "sail-else-after-terminal" l
          "The then branch does not continue; move the else branch after the conditional."
      );
      if parse_redundant_nested_if else_exp then (
        let (E_aux (_, l)) = else_exp in
        readability_warning "sail-nested-else-if" l
          "This else block contains only a conditional; write it as an else-if chain."
      )
  | E_loop (_, _, condition, _) -> warn_parse_condition condition
  | E_match (subject, _) -> warn_parse_condition subject
  | E_assert (condition, _) -> warn_parse_condition condition
  | _ -> ()
  );
  match aux with
  | E_match (subject, cases) | E_try (subject, cases) ->
      inspect_parse_exp subject;
      List.iter inspect_parse_pexp cases
  | _ -> List.iter inspect_parse_exp (parse_exp_children exp)

and inspect_parse_pexp (Parse_ast.Pat_aux (aux, _)) =
  let open Parse_ast in
  match aux with
  | Pat_exp (_, exp) -> inspect_parse_exp exp
  | Pat_when (_, guard, exp) ->
      warn_parse_condition guard;
      inspect_parse_exp guard;
      inspect_parse_exp exp
  | Pat_attribute (_, pexp) -> inspect_parse_pexp pexp

let rec inspect_parse_funcl (Parse_ast.FCL_aux (aux, _)) =
  let open Parse_ast in
  match aux with
  | FCL_funcl (_, pexp) ->
      inspect_parse_pexp pexp;
      inspect_parse_tail_pexp pexp
  | FCL_private funcl | FCL_attribute (_, funcl) | FCL_doc (_, funcl) -> inspect_parse_funcl funcl

let rec inspect_parse_mapcl (Parse_ast.MCL_aux (aux, _)) =
  let open Parse_ast in
  let inspect_mpexp (MPat_aux (aux, _)) =
    match aux with
    | MPat_pat _ -> ()
    | MPat_when (_, guard) ->
        warn_parse_condition guard;
        inspect_parse_exp guard
  in
  match aux with
  | MCL_attribute (_, mapcl) | MCL_doc (_, mapcl) -> inspect_parse_mapcl mapcl
  | MCL_bidir (left, right) ->
      inspect_mpexp left;
      inspect_mpexp right
  | MCL_forwards_deprecated (mpexp, exp) ->
      inspect_mpexp mpexp;
      inspect_parse_exp exp
  | MCL_forwards pexp | MCL_backwards pexp -> inspect_parse_pexp pexp
  | MCL_when (mapcl, guard) ->
      inspect_parse_mapcl mapcl;
      warn_parse_condition guard;
      inspect_parse_exp guard

let inspect_parse_fundef (Parse_ast.FD_aux (Parse_ast.FD_function (rec_opt, _, funcls), _)) =
  let (Parse_ast.Rec_aux (rec_aux, _)) = rec_opt in
  (match rec_aux with Parse_ast.Rec_none -> () | Parse_ast.Rec_measure (_, exp) -> inspect_parse_exp exp);
  List.iter inspect_parse_funcl funcls

let rec inspect_parse_def (Parse_ast.DEF_aux (aux, _)) =
  let open Parse_ast in
  match aux with
  | DEF_fundef fundef -> inspect_parse_fundef fundef
  | DEF_mapdef (MD_aux (MD_mapping (_, _, mapcls), _)) -> List.iter inspect_parse_mapcl mapcls
  | DEF_impl funcl -> inspect_parse_funcl funcl
  | DEF_let (_, exp) | DEF_measure (_, _, exp) -> inspect_parse_exp exp
  | DEF_outcome (_, defs) -> List.iter inspect_parse_def defs
  | DEF_scattered (SD_aux (saux, _)) -> (
      match saux with
      | SD_funcl funcl -> inspect_parse_funcl funcl
      | SD_mapcl (_, mapcl) -> inspect_parse_mapcl mapcl
      | SD_function _ | SD_enum _ | SD_enumcl _ | SD_variant _ | SD_unioncl _ | SD_mapping _ | SD_end _ -> ()
    )
  | DEF_loop_measures (_, measures) -> List.iter (fun (Loop (_, exp)) -> inspect_parse_exp exp) measures
  | DEF_register (DEC_aux (DEC_reg (_, _, initial), _)) -> Option.iter inspect_parse_exp initial
  | DEF_type (TD_aux (TD_enum (_, _, members), _)) ->
      List.iter (fun (_, value) -> Option.iter inspect_parse_exp value) members
  | DEF_private def | DEF_attribute (_, def) | DEF_doc (_, def) -> inspect_parse_def def
  | DEF_internal_mutrec fundefs -> List.iter inspect_parse_fundef fundefs
  | DEF_type _ | DEF_constraint _ | DEF_overload _ | DEF_fixity _ | DEF_val _ | DEF_instantiation _ | DEF_default _
  | DEF_pragma _ ->
      ()

let warn_parse_readability defs = List.iter inspect_parse_def defs

let count_id id exp =
  let alg = { (Rewriter.pure_exp_alg 0 ( + )) with e_id = (fun found -> if Id.compare id found = 0 then 1 else 0) } in
  Rewriter.fold_exp alg exp

let has_numbered_suffix prefix name =
  let prefix_length = String.length prefix in
  let name_length = String.length name in
  name_length > prefix_length + 1
  && String.sub name 0 prefix_length = prefix
  && name.[prefix_length] = '_'
  &&
  let rec all_digits index =
    index = name_length
    ||
    let character = name.[index] in
    character >= '0' && character <= '9' && all_digits (index + 1)
  in
  all_digits (prefix_length + 1)

let is_unhelpful_temporary_name id =
  let name = string_of_id id in
  List.exists (fun prefix -> String.equal name prefix || has_numbered_suffix prefix name) ["tmp"; "temp"]

module Scan (F : sig
  type t
  val do_exp : t exp -> unit
  val do_funcl_pexp : (t pat -> t exp option -> t exp -> unit) option
end) : sig
  val in_def : (F.t, 'b) def -> unit
end = struct
  let in_pexp (Pat_aux (aux, _)) =
    match aux with
    | Pat_exp (_, exp) -> F.do_exp exp
    | Pat_when (_, guard, exp) ->
        F.do_exp guard;
        F.do_exp exp

  let in_funcl (FCL_aux (FCL_funcl (_, pexp), _)) =
    match F.do_funcl_pexp with
    | Some g -> (
        match pexp with
        | Pat_aux (Pat_exp (pat, exp), _) -> g pat None exp
        | Pat_aux (Pat_when (pat, guard, exp), _) -> g pat (Some guard) exp
      )
    | None -> in_pexp pexp

  let in_mpexp (MPat_aux (aux, _)) = match aux with MPat_when (_, exp) -> F.do_exp exp | MPat_pat _ -> ()

  let in_mapcl (MCL_aux (aux, _)) =
    match aux with
    | MCL_forwards pexp | MCL_backwards pexp -> in_pexp pexp
    | MCL_bidir (left, right) ->
        in_mpexp left;
        in_mpexp right

  let in_scattered_def (SD_aux (aux, _)) =
    match aux with
    | SD_function _ | SD_unioncl _ | SD_variant _ | SD_internal_unioncl_record _ | SD_enumcl _ | SD_enum _
    | SD_mapping _ | SD_end _ ->
        ()
    | SD_funcl funcl -> in_funcl funcl
    | SD_mapcl (_, mapcl) -> in_mapcl mapcl

  let in_fundef (FD_aux (FD_function (_, _, funcls), _)) = List.iter in_funcl funcls

  let rec in_def (DEF_aux (aux, _)) =
    match aux with
    | DEF_fundef fdef -> in_fundef fdef
    | DEF_mapdef (MD_aux (MD_mapping (_, _, mapcls), _)) -> List.iter in_mapcl mapcls
    | DEF_register (DEC_aux (DEC_reg (_, _, exp_opt), _)) -> Option.iter F.do_exp exp_opt
    | DEF_outcome (_, defs) -> List.iter in_def defs
    | DEF_impl funcl -> in_funcl funcl
    | DEF_let (_, exp) -> F.do_exp exp
    | DEF_scattered sdef -> in_scattered_def sdef
    | DEF_internal_mutrec fdefs -> List.iter in_fundef fdefs
    | DEF_loop_measures _ -> ()
    | DEF_measure (_, _, exp) -> F.do_exp exp
    | DEF_type _ | DEF_constraint _ | DEF_val _ | DEF_fixity _ | DEF_overload _ | DEF_default _ | DEF_pragma _
    | DEF_instantiation _ ->
        ()
end

let warn_readability effect_info ast =
  (* Attach inferred transitive effects before scanning.  Rules that remove
     or move an expression require an empty effect set; structural rules that
     preserve evaluation count may inspect effectful expressions. *)
  let ast = Effects.rewrite_attach_effects effect_info ast in
  let inspect (e_aux, annot) =
    let exp = E_aux (e_aux, annot) in
    let l = exp_loc exp in
    ( match e_aux with
    | E_app (id, [E_aux (E_app (inner, [_]), _)]) when is_app "not_bool" id && is_app "not_bool" inner ->
        readability_warning "sail-redundant-bool" l "Double boolean negation can be removed."
    | E_app (id, [argument]) when is_app "not_bool" id && Option.is_some (bool_literal argument) ->
        readability_warning "sail-redundant-bool" l "Negating a boolean literal is a constant expression."
    | E_app (id, [lhs; rhs]) when is_app "eq_bool" id || is_app "neq_bool" id -> (
        match (bool_literal lhs, bool_literal rhs) with
        | Some _, _ | _, Some _ ->
            readability_warning "sail-redundant-bool" l
              "A boolean comparison with true or false can be written directly (or negated)."
        | _ -> ()
      )
    | E_if (condition, then_exp, else_exp) ->
        if
          (not (effectful (Type_check.effect_of condition)))
          && expressions_equal then_exp else_exp
          && not (is_unit_literal then_exp && is_unit_literal else_exp)
        then
          readability_warning "sail-duplicate-branches" l
            "Both branches are identical and the condition is pure; remove the conditional.";
        if (not (effectful (Type_check.effect_of condition))) && is_unit_literal then_exp && is_unit_literal else_exp
        then
          readability_warning "sail-empty-conditional" l
            "Both branches are empty and the condition is pure; remove the conditional.";
        ( match (simple_assignment then_exp, simple_assignment else_exp) with
        | Some (then_id, _), Some (else_id, _) when Id.compare then_id else_id = 0 ->
            readability_warning "sail-conditional-assignment" l
              "Both branches assign the same local; assign one conditional value instead."
        | _ -> ()
        );
        ()
    | E_let (P_aux (P_id bound, _), _, E_aux (E_id result, _)) when Id.compare bound result = 0 ->
        readability_warning "sail-trivial-alias" l
          "This binding is returned unchanged; return the bound expression directly."
    | E_let (P_aux (P_id bound, _), binding, body)
      when is_unhelpful_temporary_name bound
           && (not (effectful (Type_check.effect_of binding)))
           && count_id bound body = 1 ->
        readability_warning "sail-single-use-temporary" l
          "This generically named pure binding is used once; inline it or give the intermediate a semantic name."
    | E_let (P_aux (P_wild, _), binding, _) when not (effectful (Type_check.effect_of binding)) ->
        readability_warning "sail-dead-pure-binding" l
          "This pure wildcard binding has no observable effect and can be removed."
    | _ -> ()
    );
    exp
  in
  let alg = { Rewriter.id_exp_alg with e_aux = inspect } in
  let module S = Scan (struct
    type t = Type_check.tannot
    let do_exp exp = ignore (Rewriter.fold_exp alg exp)
    let do_funcl_pexp = None
  end) in
  List.iter S.in_def ast.defs

let warn_unmodified_variables (type a) (ast : (a, 'b) ast) : unit =
  let warn_unmodified (lexp, bind, exp) =
    let unmodified = IdSet.diff lexp exp in
    IdSet.iter
      (fun id ->
        Reporting.warn "Unnecessary mutability" (id_loc id)
          "This variable is mutable, but it is never modified. It could be declared as immutable using 'let'."
      )
      unmodified;
    IdSet.union (IdSet.diff exp lexp) bind
  in
  let alg =
    {
      (Rewriter.pure_exp_alg IdSet.empty IdSet.union) with
      le_id = IdSet.singleton;
      le_typ = (fun (_, id) -> IdSet.singleton id);
      e_var = warn_unmodified;
    }
  in
  let module S = Scan (struct
    type t = a
    let do_exp exp = ignore (Rewriter.fold_exp alg exp)
    let do_funcl_pexp = None
  end) in
  List.iter S.in_def ast.defs

let warn_unused_variables (ast : Type_check.typed_ast) : unit =
  let ignore_variable id = (string_of_id id).[0] = '_' || is_gen_loc (id_loc id) in
  let pexp_unused pat guard_opt exp =
    let used = IdSet.union exp (Option.value ~default:IdSet.empty guard_opt) in
    let unused = IdSet.diff pat used in
    IdSet.iter
      (fun id ->
        if not (ignore_variable id) then
          Reporting.warn "Unused variable" (id_loc id) "This variable is defined but never used."
      )
      unused;
    IdSet.diff used pat
  in
  (* Gather all the variables defined by a pattern *)
  let pat_alg env =
    {
      (Rewriter.pure_pat_alg IdSet.empty IdSet.union) with
      p_id = (fun id -> if Type_check.is_enum_member id env then IdSet.empty else IdSet.singleton id);
      p_vector_subrange = (fun (id, _, _) -> IdSet.singleton id);
      p_as = (fun (_, id) -> IdSet.singleton id);
    }
  in
  let alg env =
    {
      (Rewriter.pure_exp_alg IdSet.empty IdSet.union) with
      e_id = IdSet.singleton;
      pat_exp = (fun (pat, exp) -> pexp_unused pat None exp);
      pat_when = (fun (pat, guard, exp) -> pexp_unused pat (Some guard) exp);
      pat_alg = pat_alg env;
    }
  in
  let module S = Scan (struct
    type t = Type_check.tannot
    let do_exp exp = ignore (Rewriter.fold_exp (alg (Type_check.env_of exp)) exp)
    let do_funcl_pexp =
      Some
        (fun pat guard_opt exp ->
          let env = Type_check.env_of_pat pat in
          let pat = Rewriter.fold_pat (pat_alg env) pat in
          let guard_opt = Option.map (Rewriter.fold_exp (alg env)) guard_opt in
          let exp = Rewriter.fold_exp (alg env) exp in
          ignore (pexp_unused pat guard_opt exp)
        )
  end) in
  List.iter S.in_def ast.defs
