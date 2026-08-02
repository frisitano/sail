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

open Libsail

open Ast
open Ast_compare
open Ast_util
open Bit
open Jib
open Jib_compile
open Jib_util
open Jib_visitor
open Type_check
open PPrint
open Value2
module Document = Pretty_print_sail.Document

open Anf

module Big_int = Nat_big_num

let opt_prefix = ref "z"
let opt_extra_params = ref None
let opt_extra_arguments = ref None

let extra_params () = match !opt_extra_params with Some str -> str ^ ", " | _ -> ""

let extra_arguments is_extern = match !opt_extra_arguments with Some str when not is_extern -> str ^ ", " | _ -> ""

(* Optimization flags *)
let optimize_primops = ref false
let optimize_hoist_allocations = ref false
let optimize_alias = ref false
let optimize_fixed_int = ref false
let optimize_fixed_bits = ref false

let ngensym = symbol_generator ()

let c_error ?loc:(l = Parse_ast.Unknown) message = raise (Reporting.err_general l ("\nC backend: " ^ message))

(**************************************************************************)
(* Converting Sail types to C types                                       *)
(**************************************************************************)

let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))
let max_uint n = Big_int.pred (Big_int.pow_int_positive 2 n)
let native_integer_widths = [8; 16; 32; 64]

let smallest_native_integer_ctyp lower upper =
  if Big_int.less_equal Big_int.zero lower then
    List.find_map
      (fun width -> if Big_int.less_equal upper (max_uint width) then Some (CT_fuint width) else None)
      native_integer_widths
  else
    List.find_map
      (fun width ->
        if Big_int.less_equal (min_int width) lower && Big_int.less_equal upper (max_int width) then Some (CT_fint width)
        else None
      )
      native_integer_widths

(* C-only opaque JIB markers for representations that have no general-purpose
   JIB equivalent.  Encoding them as reserved synthetic structs keeps the
   representation choice local to the C backend: the Sail and proof backends
   continue to see bits(256) and vector(N, byte), while C gets POD value types. *)
let c_repr_u128_id = mk_id "__sail_c_repr_u128"
let c_repr_u256_id = mk_id "__sail_c_repr_u256"
let c_repr_u320_id = mk_id "__sail_c_repr_u320"
let c_repr_fixed_bytes_id = mk_id "__sail_c_repr_fixed_bytes"
let c_repr_u128_ctyp = CT_struct (c_repr_u128_id, [])
let c_repr_u256_ctyp = CT_struct (c_repr_u256_id, [])
let c_repr_u320_ctyp = CT_struct (c_repr_u320_id, [])
let c_repr_fixed_bytes_ctyp n = CT_struct (c_repr_fixed_bytes_id, [CT_constant (Big_int.of_int n)])

let is_c_repr_u128 = function CT_struct (id, []) -> Id.compare id c_repr_u128_id = 0 | _ -> false

let is_c_repr_u256 = function CT_struct (id, []) -> Id.compare id c_repr_u256_id = 0 | _ -> false

let is_c_repr_u320 = function CT_struct (id, []) -> Id.compare id c_repr_u320_id = 0 | _ -> false

let c_repr_fixed_bytes_length = function
  | CT_struct (id, [CT_constant n]) when Id.compare id c_repr_fixed_bytes_id = 0 -> (
      try Some (Big_int.to_int n) with _ -> None
    )
  | _ -> None

let is_c_repr_fixed_bytes ctyp = Option.is_some (c_repr_fixed_bytes_length ctyp)
let is_c_repr_value ctyp =
  is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp || is_c_repr_fixed_bytes ctyp

let rec ctyp_suprema_for_c specialize = function
  | ctyp when specialize && is_c_repr_value ctyp -> ctyp
  | (CT_fint _ | CT_fuint _ | CT_fbits _ | CT_sbits _) as ctyp when specialize -> ctyp
  | CT_tup ctyps when specialize -> CT_tup (List.map (ctyp_suprema_for_c specialize) ctyps)
  | CT_vector ctyp when specialize -> CT_vector (ctyp_suprema_for_c specialize ctyp)
  | CT_fvector (length, ctyp) when specialize -> CT_fvector (length, ctyp_suprema_for_c specialize ctyp)
  | CT_list ctyp when specialize -> CT_list (ctyp_suprema_for_c specialize ctyp)
  | CT_ref ctyp when specialize -> CT_ref (ctyp_suprema_for_c specialize ctyp)
  | ctyp -> Jib_util.ctyp_suprema ctyp

(** This function is used to split types into those we allocate on the stack, versus those which need to live on the
    heap, or otherwise require some additional memory management.

    This is roughly the same distinction that Rust makes between copy and non-copy types. *)
let rec is_stack_ctyp ctx ctyp =
  match ctyp with
  | ctyp when is_c_repr_value ctyp -> true
  | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_enum _ -> true
  | CT_fint n -> n <= 128
  | CT_fuint n -> n <= 64
  | CT_lint when !optimize_fixed_int -> true
  | CT_lint -> false
  | CT_lbits when !optimize_fixed_bits -> true
  | CT_lbits -> false
  | CT_real | CT_string | CT_list _ | CT_vector _ -> false
  | CT_fvector (_, ctyp) -> is_stack_ctyp ctx ctyp
  | CT_struct (_, _) ->
      let _, fields = struct_field_bindings Parse_ast.Unknown ctx ctyp in
      Bindings.for_all (fun _ ctyp -> is_stack_ctyp ctx ctyp) fields
  | CT_variant _ as ctyp ->
      let _, constructors = variant_constructor_bindings Parse_ast.Unknown ctx ctyp in
      Bindings.for_all (fun _ ctyp -> is_stack_ctyp ctx ctyp) constructors
  | CT_tup ctyps -> List.for_all (is_stack_ctyp ctx) ctyps
  | CT_ref _ -> true
  | CT_poly _ -> true
  | CT_float _ -> true
  | CT_rounding_mode -> true
  (* Is a reference to some immutable JSON data *)
  | CT_json -> true
  | CT_json_key -> true
  | CT_constant n -> Big_int.less_equal (min_int 64) n && Big_int.less_equal n (max_int 64)
  | CT_memory_writes -> false

let v_mask_lower i = V_lit (VL_bits (Util.list_init i (fun _ -> Sail2_values.B1)), CT_fbits i)

let hex_char =
  let open Sail2_values in
  function
  | '0' -> [B0; B0; B0; B0]
  | '1' -> [B0; B0; B0; B1]
  | '2' -> [B0; B0; B1; B0]
  | '3' -> [B0; B0; B1; B1]
  | '4' -> [B0; B1; B0; B0]
  | '5' -> [B0; B1; B0; B1]
  | '6' -> [B0; B1; B1; B0]
  | '7' -> [B0; B1; B1; B1]
  | '8' -> [B1; B0; B0; B0]
  | '9' -> [B1; B0; B0; B1]
  | 'A' | 'a' -> [B1; B0; B1; B0]
  | 'B' | 'b' -> [B1; B0; B1; B1]
  | 'C' | 'c' -> [B1; B1; B0; B0]
  | 'D' | 'd' -> [B1; B1; B0; B1]
  | 'E' | 'e' -> [B1; B1; B1; B0]
  | 'F' | 'f' -> [B1; B1; B1; B1]
  | _ -> failwith "Invalid hex character"

let literal_to_fragment ctyp (L_aux (l_aux, _)) =
  match l_aux with
  | L_num n -> (
      match ctyp with
      | ctyp when is_c_repr_u320 ctyp && Big_int.less_equal Big_int.zero n && Big_int.less_equal n (max_uint 320) ->
          Some (V_lit (VL_int n, ctyp))
      | ctyp when is_c_repr_u256 ctyp && Big_int.less_equal Big_int.zero n && Big_int.less_equal n (max_uint 256) ->
          Some (V_lit (VL_int n, ctyp))
      | ctyp when is_c_repr_u128 ctyp && Big_int.less_equal Big_int.zero n && Big_int.less_equal n (max_uint 128) ->
          Some (V_lit (VL_int n, ctyp))
      | CT_fuint width when Big_int.less_equal Big_int.zero n && Big_int.less_equal n (max_uint width) ->
          Some (V_lit (VL_int n, ctyp))
      | CT_fint width when Big_int.less_equal (min_int width) n && Big_int.less_equal n (max_int width) ->
          Some (V_lit (VL_int n, ctyp))
      | CT_constant value
        when Big_int.equal value n && Big_int.less_equal (min_int 64) n && Big_int.less_equal n (max_int 64) ->
          Some (V_lit (VL_int n, ctyp))
      | _ when Big_int.less_equal (min_int 64) n && Big_int.less_equal n (max_int 64) ->
          Some (V_lit (VL_int n, CT_fint 64))
      | _ -> None
    )
  | L_bin bin ->
      let len = bin_lit_length bin in
      if len <= 64 || (is_c_repr_u256 ctyp && len <= 256) then (
        let content = BitList.of_bin_lit bin |> List.map (function B0 -> Sail2_values.B0 | B1 -> Sail2_values.B1) in
        Some (V_lit (VL_bits content, if is_c_repr_u256 ctyp then ctyp else CT_fbits len))
      )
      else None
  | L_hex hex ->
      let len = hex_lit_length hex in
      if len <= 64 || (is_c_repr_u256 ctyp && len <= 256) then (
        let content = BitList.of_hex_lit hex |> List.map (function B0 -> Sail2_values.B0 | B1 -> Sail2_values.B1) in
        Some (V_lit (VL_bits content, if is_c_repr_u256 ctyp then ctyp else CT_fbits len))
      )
      else None
  | L_unit -> Some (V_lit (VL_unit, CT_unit))
  | L_true -> Some (V_lit (VL_bool true, CT_bool))
  | L_false -> Some (V_lit (VL_bool false, CT_bool))
  | _ -> None

let sail_create ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sCREATE(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_recreate ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sRECREATE(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_copy ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sCOPY(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_kill ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sKILL(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_equal ?(prefix = "") ?(suffix = "") ctyp fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sEQUAL(%s)(%s)%s" prefix ctyp s suffix) fmt

let sail_convert_of ?(prefix = "") ?(suffix = "") ctyp1 ctyp2 fmt =
  let open Printf in
  ksprintf (fun s -> ksprintf string "%sCONVERT_OF(%s, %s)(%s)%s" prefix ctyp1 ctyp2 s suffix) fmt

let c_function ~return decl body =
  string return ^^ space ^^ decl ^^ space ^^ nest 2 (lbrace ^^ hardline ^^ separate hardline body) ^^ hardline ^^ rbrace

let c_stmt s = string s ^^ semi

let c_assign x op y = separate space [x; string op; y] ^^ semi

let c_for iter body =
  string "for" ^^ space ^^ iter ^^ space ^^ nest 2 (lbrace ^^ hardline ^^ separate hardline body) ^^ hardline ^^ rbrace

let c_cond_block c block = if c then block else []

let c_if_block b = nest 2 (lbrace ^^ hardline ^^ separate hardline b) ^^ hardline ^^ rbrace

let c_if cond then_block = string "if" ^^ space ^^ cond ^^ space ^^ c_if_block then_block

let c_if_else cond then_block else_block =
  string "if" ^^ space ^^ cond ^^ space ^^ c_if_block then_block ^^ space ^^ string "else" ^^ space
  ^^ c_if_block else_block

let c_return exp = string "return" ^^ space ^^ exp ^^ semi

let c_case_block b = nest 2 (separate hardline ([lbrace] @ b @ [c_stmt "break"])) ^^ hardline ^^ rbrace

(* Generate a C switch statement. If default is true, then we generate a `default: break;` case at the end. *)
let c_switch ?(default = false) cond cases =
  match cases with
  | [] -> string "{}"
  | _ ->
      string "switch" ^^ space ^^ cond ^^ space ^^ lbrace ^^ hardline
      ^^ separate_map hardline
           (fun (case_exp, case_block) ->
             string "case" ^^ space ^^ case_exp ^^ colon ^^ space ^^ c_case_block case_block
           )
           cases
      ^^ (if default then hardline ^^ string "default" ^^ colon ^^ space ^^ string "break" ^^ semi else empty)
      ^^ hardline ^^ rbrace

module C_config (Opts : sig
  val branch_coverage : out_channel option
  val assert_to_exception : bool
  val preserve_types : IdSet.t
  val c_repr_unsigned : int Bindings.t
  val c_repr_signed : int Bindings.t
  val c_repr_u256 : IdSet.t
  val c_repr_fixed_bytes : int Bindings.t
  val specialize_c : bool
  val require_bounded_int : bool
  val optimized_model : bool
end) : CONFIG = struct
  let specialize_c = Opts.specialize_c
  let require_bounded_int = Opts.require_bounded_int

  (* Representation annotations are C-only and may sit behind one or more
     transparent Sail aliases. Inspect that chain before expand_synonyms erases
     the semantic type names. *)
  let rec find_c_repr_integer representations env (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_id id -> (
        match Bindings.find_opt id representations with
        | Some width -> Some width
        | None -> (
            match Bindings.find_opt id (Env.get_typ_synonyms env) with
            | Some ([], A_aux (A_typ typ, _)) -> find_c_repr_integer representations env typ
            | _ -> None
          )
      )
    | _ -> None

  let rec has_c_repr_u256 env (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_id id when IdSet.mem id Opts.c_repr_u256 -> true
    | Typ_id id -> (
        match Bindings.find_opt id (Env.get_typ_synonyms env) with
        | Some ([], A_aux (A_typ typ, _)) -> has_c_repr_u256 env typ
        | _ -> false
      )
    | _ -> false

  let rec find_c_repr_fixed_bytes env (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_id id -> (
        match Bindings.find_opt id Opts.c_repr_fixed_bytes with
        | Some length -> Some length
        | None -> (
            match Bindings.find_opt id (Env.get_typ_synonyms env) with
            | Some ([], A_aux (A_typ typ, _)) -> find_c_repr_fixed_bytes env typ
            | _ -> None
          )
      )
    | _ -> None

  let ctyp_suprema = ctyp_suprema_for_c Opts.specialize_c

  let specialize_newtype_payload id ctyp =
    if Opts.specialize_c && Bindings.mem id Opts.c_repr_unsigned then CT_fuint (Bindings.find id Opts.c_repr_unsigned)
    else if Opts.specialize_c && Bindings.mem id Opts.c_repr_signed then CT_fint (Bindings.find id Opts.c_repr_signed)
    else if Opts.specialize_c && IdSet.mem id Opts.c_repr_u256 then c_repr_u256_ctyp
    else (
      match Bindings.find_opt id Opts.c_repr_fixed_bytes with
      | Some length when Opts.specialize_c -> c_repr_fixed_bytes_ctyp length
      | _ -> (
          match ctyp with
          | CT_fvector (length, CT_fbits 8) when Opts.specialize_c && length > 0 -> c_repr_fixed_bytes_ctyp length
          | _ -> ctyp
        )
    )

  let specializes_narrow_fixed_integer ~semantic ~represented =
    match (semantic, represented) with
    | (CT_fint semantic_width | CT_fuint semantic_width), (CT_fint represented_width | CT_fuint represented_width) ->
        represented_width < semantic_width
    | _ -> false

  let rec representation_refines ~semantic ~represented =
    match (semantic, represented) with
    | semantic, represented when specializes_narrow_fixed_integer ~semantic ~represented -> true
    | CT_lint, (CT_fint _ | CT_fuint _) -> true
    | CT_lint, represented when is_c_repr_u128 represented || is_c_repr_u256 represented || is_c_repr_u320 represented
      ->
        true
    | CT_lbits, represented when is_c_repr_u256 represented -> true
    | semantic, CT_fuint _ when is_c_repr_u128 semantic || is_c_repr_u256 semantic || is_c_repr_u320 semantic -> true
    | semantic, represented
      when (is_c_repr_u256 semantic && is_c_repr_u128 represented)
           || (is_c_repr_u320 semantic && (is_c_repr_u128 represented || is_c_repr_u256 represented)) ->
        true
    | (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented when is_c_repr_fixed_bytes represented -> true
    | CT_vector semantic_element, CT_fvector (_, represented_element) ->
        ctyp_equal semantic_element represented_element
        || representation_refines ~semantic:semantic_element ~represented:represented_element
    | _ -> false

  (* The Sail typechecker has already proved the actual argument inhabits the
     semantic parameter type.  When its selected fixed representation is
     strictly narrower, retain it by cloning the local function instead of
     inserting a widening conversion at the call boundary. *)
  let specialize_function_argument_representation ~semantic ~represented =
    Opts.specialize_c
    && (specializes_narrow_fixed_integer ~semantic ~represented
       ||
       match (semantic, represented) with
       | CT_lint, (CT_fint _ | CT_fuint _) -> true
       | CT_lint, represented
         when is_c_repr_u128 represented || is_c_repr_u256 represented || is_c_repr_u320 represented ->
           true
       | semantic, CT_fuint _ when is_c_repr_u128 semantic || is_c_repr_u256 semantic || is_c_repr_u320 semantic -> true
       | semantic, represented
         when (is_c_repr_u256 semantic && is_c_repr_u128 represented)
              || (is_c_repr_u320 semantic && (is_c_repr_u128 represented || is_c_repr_u256 represented)) ->
           true
       | CT_lbits, represented when is_c_repr_u256 represented -> true
       | (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented when is_c_repr_fixed_bytes represented ->
           true
       | CT_vector semantic_element, CT_fvector (_, represented_element) ->
           ctyp_equal semantic_element represented_element
           || representation_refines ~semantic:semantic_element ~represented:represented_element
       | _ -> false
       )

  let specialize_function_result_representation ~semantic ~represented =
    Opts.specialize_c
    && (specializes_narrow_fixed_integer ~semantic ~represented
       ||
       match (semantic, represented) with
       | CT_lint, (CT_fint _ | CT_fuint _) -> true
       | CT_lint, represented
         when is_c_repr_u128 represented || is_c_repr_u256 represented || is_c_repr_u320 represented ->
           true
       | CT_lbits, represented when is_c_repr_u256 represented -> true
       | (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented when is_c_repr_fixed_bytes represented ->
           true
       | CT_vector semantic_element, CT_fvector (_, represented_element) ->
           ctyp_equal semantic_element represented_element
           || representation_refines ~semantic:semantic_element ~represented:represented_element
       | _ -> false
       )

  let specialize_function_body_representation = specialize_function_result_representation

  let integer_representation_bounds = function
    | CT_fuint width -> Some (Big_int.zero, max_uint width)
    | CT_fint width -> Some (min_int width, max_int width)
    | ctyp when is_c_repr_u128 ctyp -> Some (Big_int.zero, max_uint 128)
    | ctyp when is_c_repr_u256 ctyp -> Some (Big_int.zero, max_uint 256)
    | ctyp when is_c_repr_u320 ctyp -> Some (Big_int.zero, max_uint 320)
    | CT_constant value -> Some (value, value)
    | _ -> None

  let specialized_function_external id param_ctyps ret_ctyp =
    let fixed_integer = function CT_fint _ | CT_fuint _ -> true | _ -> false in
    let fixed_bytes_at_most_32 = function
      | ctyp -> (
          match c_repr_fixed_bytes_length ctyp with Some length -> length <= 32 | None -> false
        )
    in
    if not Opts.specialize_c then None
    else (
      match (string_of_id id, param_ctyps, ret_ctyp) with
      | "from_bytes_le", [width; bytes], ret
        when fixed_integer width && fixed_bytes_at_most_32 bytes && is_c_repr_u256 ret ->
          Some (mk_id "__sail_from_bytes_le_fixed_u256")
      | "to_bytes_le", [width; bits], ret when fixed_integer width && is_c_repr_u256 bits && fixed_bytes_at_most_32 ret
        ->
          Some (mk_id "__sail_to_bytes_le_u256_fixed")
      | "alu_addmod", [left; right; modulus], ret
        when List.for_all is_c_repr_u256 [left; right; modulus] && is_c_repr_u256 ret ->
          Some (mk_id "__sail_u256_addmod")
      | "alu_mulmod", [left; right; modulus], ret
        when List.for_all is_c_repr_u256 [left; right; modulus] && is_c_repr_u256 ret ->
          Some (mk_id "__sail_u256_mulmod")
      | _ -> None
    )

  let function_argument_unification_type ~expected ~represented =
    match (c_repr_fixed_bytes_length expected, expected, represented, c_repr_fixed_bytes_length represented) with
    | Some expected_length, _, CT_fvector (represented_length, CT_fbits 8), _ when expected_length = represented_length
      ->
        Some expected
    | Some _, _, CT_vector (CT_fbits 8), _ -> Some expected
    | None, (CT_vector _ | CT_fvector _), _, Some length -> Some (CT_fvector (length, CT_fbits 8))
    | None, CT_vector semantic_element, (CT_fvector (_, represented_element) as represented), None
      when ctyp_equal semantic_element represented_element
           || representation_refines ~semantic:semantic_element ~represented:represented_element ->
        Some represented
    | _ when specializes_narrow_fixed_integer ~semantic:expected ~represented -> Some expected
    | _ -> None

  let function_argument_narrowing_allowed ~expected ~source:_ ~represented =
    ((is_c_repr_u128 expected || is_c_repr_u256 expected || is_c_repr_u320 expected)
     && ctyp_equal represented CT_lint
    ||
    match expected with
    | CT_fuint _ -> is_c_repr_u128 represented || is_c_repr_u256 represented || is_c_repr_u320 represented
    | _ -> false
    )

  (* Flow typing can refine a local integer to a range whose preferred native
     signedness differs from the C type selected when the storage was
     declared.  The important representation for an occurrence of that local
     is its actual storage type: both CT_fint and CT_fuint are stack values,
     and changing flow facts must not make the optimizer pretend the value is
     heap-backed.  This is intentionally local-storage compatibility rather
     than a general representation refinement rule. *)
  let fixed_integer_storage_compatible ~semantic ~represented =
    match (semantic, represented) with
    | (CT_fint semantic_width | CT_fuint semantic_width), (CT_fint represented_width | CT_fuint represented_width) ->
        semantic_width = represented_width
    | semantic, represented
      when (is_c_repr_u128 semantic && (is_c_repr_u256 represented || is_c_repr_u320 represented))
           || (is_c_repr_u256 semantic && is_c_repr_u320 represented) ->
        true
    | _ -> false

  let preserve_aval_representation ~semantic ~represented =
    match semantic with
    | CT_lint -> (
        match represented with
        | CT_fint _ | CT_fuint _ -> true
        | represented -> is_c_repr_u128 represented || is_c_repr_u256 represented || is_c_repr_u320 represented
      )
    | CT_lbits -> is_c_repr_u256 represented
    | CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8) -> is_c_repr_fixed_bytes represented
    | CT_vector semantic_element -> (
        match represented with
        | CT_fvector (_, represented_element) ->
            ctyp_equal semantic_element represented_element
            || representation_refines ~semantic:semantic_element ~represented:represented_element
        | _ -> false
      )
    | _ -> false

  let propagate_newtype_payload_representation id ~semantic ~represented =
    representation_refines ~semantic ~represented
    || ( match Bindings.find_opt id Opts.c_repr_unsigned with
      | Some width -> ctyp_equal represented (CT_fuint width)
      | None -> false
      )
    || ( match Bindings.find_opt id Opts.c_repr_signed with
      | Some width -> ctyp_equal represented (CT_fint width)
      | None -> false
      )
    || (IdSet.mem id Opts.c_repr_u256 && is_c_repr_u256 represented)
    ||
    match Bindings.find_opt id Opts.c_repr_fixed_bytes with
    | Some length when Opts.specialize_c -> ctyp_equal represented (c_repr_fixed_bytes_ctyp length)
    | _ -> false

  let specialize_call_result id arg_ctyps semantic =
    let fixed_bytes_at_most_32 = function
      | ctyp -> (
          match c_repr_fixed_bytes_length ctyp with Some length -> length <= 32 | None -> false
        )
    in
    let preserves_first_argument =
      match string_of_id id with
      | "vector_update" | "vector_update_inc" | "internal_vector_update" | "add_bits" | "sub_bits" | "not_bits"
      | "and_bits" | "or_bits" | "xor_bits" | "mult_vec" | "mults_vec" | "shiftl" | "shiftr" | "arith_shiftr" ->
          true
      | _ -> false
    in
    match (string_of_id id, arg_ctyps, semantic) with
    | "from_bytes_le", [(CT_fint _ | CT_fuint _); bytes], CT_lbits when fixed_bytes_at_most_32 bytes -> c_repr_u256_ctyp
    | _ -> (
        match (preserves_first_argument, arg_ctyps) with
        | true, represented :: _ when representation_refines ~semantic ~represented -> represented
        | _ -> semantic
      )

  let specialize_call_destination ctx id arg_ctyps ~semantic ~represented =
    let external_name = if ctx_is_extern id ctx then ctx_get_extern id ctx else string_of_id id in
    let specialized = specialize_call_result (mk_id external_name) arg_ctyps semantic in
    if ctyp_equal specialized represented then true
    else (
      match (external_name, semantic, represented, arg_ctyps) with
      | ("zero_extend" | "sail_zero_extend"), CT_lbits, represented, (CT_fbits _ | CT_lbits) :: _
        when is_c_repr_u256 represented ->
          true
      | "vector_init", (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented, _
        when is_c_repr_fixed_bytes represented ->
          true
      | "vector_init", CT_vector semantic_element, (CT_fvector _ as represented), _
        when representation_refines ~semantic:(CT_vector semantic_element) ~represented ->
          true
      | _ -> false
    )

  let specialize_call_argument ctx id return_ctyp arg_ctyps index ~semantic ~represented =
    let external_name = if ctx_is_extern id ctx then ctx_get_extern id ctx else string_of_id id in
    let first_argument_is_fixed_bytes =
      match arg_ctyps with first :: _ -> is_c_repr_fixed_bytes first | [] -> false
    in
    let first_argument_is_vector =
      match arg_ctyps with
      | first :: _ when is_c_repr_u256 first -> true
      | (CT_vector _ | CT_fvector _) :: _ -> true
      | _ -> false
    in
    let arguments_share_fixed_bytes =
      match arg_ctyps with [left; right] -> is_c_repr_fixed_bytes left && ctyp_equal left right | _ -> false
    in
    match (external_name, return_ctyp, index, semantic, represented) with
    | "eq_anything", CT_bool, (0 | 1), (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented
      when arguments_share_fixed_bytes && is_c_repr_fixed_bytes represented ->
        true
    | ( ("vector_access" | "vector_access_inc" | "fast_vector_access"),
        _,
        0,
        (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)),
        represented )
      when is_c_repr_fixed_bytes represented ->
        true
    | ("vector_access" | "vector_access_inc" | "fast_vector_access"), _, 0, CT_lbits, represented
      when is_c_repr_u256 represented ->
        true
    | ( ("vector_access" | "vector_access_inc" | "fast_vector_access" | "fast_unsigned_vector_access"),
        _,
        1,
        CT_lint,
        (CT_fint _ | CT_fuint _) )
      when first_argument_is_fixed_bytes || first_argument_is_vector ->
        true
    | ( ("vector_access" | "vector_access_inc" | "fast_vector_access" | "fast_unsigned_vector_access"),
        _,
        0,
        CT_vector semantic_element,
        (CT_fvector _ as represented) )
      when representation_refines ~semantic:(CT_vector semantic_element) ~represented ->
        true
    | "vector_init", return_ctyp, 0, CT_lint, (CT_fint _ | CT_fuint _)
      when is_c_repr_fixed_bytes return_ctyp || match return_ctyp with CT_vector _ | CT_fvector _ -> true | _ -> false
      ->
        true
    | ( ("add_bits" | "sub_bits" | "and_bits" | "or_bits" | "xor_bits" | "mult_vec" | "mults_vec"),
        return_ctyp,
        (0 | 1),
        CT_lbits,
        represented )
      when is_c_repr_u256 return_ctyp && is_c_repr_u256 represented ->
        true
    | ("not_bits" | "shiftl" | "shiftr" | "arith_shiftr"), return_ctyp, 0, CT_lbits, represented
      when is_c_repr_u256 return_ctyp && is_c_repr_u256 represented ->
        true
    | ("shiftl" | "shiftr" | "arith_shiftr"), return_ctyp, 1, CT_lint, (CT_fint _ | CT_fuint _)
      when is_c_repr_u256 return_ctyp ->
        true
    | ("zero_extend" | "sail_zero_extend"), return_ctyp, 0, CT_lbits, (CT_fbits _ | CT_lbits)
      when is_c_repr_u256 return_ctyp ->
        true
    | ("zero_extend" | "sail_zero_extend"), return_ctyp, 1, CT_lint, (CT_fint _ | CT_fuint _)
      when is_c_repr_u256 return_ctyp ->
        true
    | ( ("vector_update" | "vector_update_inc" | "internal_vector_update"),
        return_ctyp,
        0,
        (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)),
        represented )
      when is_c_repr_fixed_bytes return_ctyp && ctyp_equal return_ctyp represented ->
        true
    | ( ("vector_update" | "vector_update_inc" | "internal_vector_update"),
        return_ctyp,
        0,
        CT_vector semantic_element,
        (CT_fvector _ as represented) )
      when ctyp_equal return_ctyp represented
           && representation_refines ~semantic:(CT_vector semantic_element) ~represented ->
        true
    | ("vector_update" | "vector_update_inc" | "internal_vector_update"), return_ctyp, 0, CT_lbits, represented
      when is_c_repr_u256 return_ctyp && is_c_repr_u256 represented ->
        true
    | ( ("vector_update" | "vector_update_inc" | "internal_vector_update"),
        return_ctyp,
        1,
        CT_lint,
        (CT_fint _ | CT_fuint _) )
      when is_c_repr_fixed_bytes return_ctyp || is_c_repr_u256 return_ctyp
           || match return_ctyp with CT_vector _ | CT_fvector _ -> true | _ -> false ->
        true
    | _ -> false

  (** Convert a sail type into a C-type. This function can be quite slow, because it uses ctx.local_env and SMT to
      analyse the Sail types and attempts to fit them into the smallest possible C types, provided ctx.optimize_smt is
      true (default) **)
  let rec convert_typ ctx typ =
    let c_repr_unsigned = find_c_repr_integer Opts.c_repr_unsigned ctx.local_env typ in
    let c_repr_signed = find_c_repr_integer Opts.c_repr_signed ctx.local_env typ in
    let c_repr_u256 = has_c_repr_u256 ctx.local_env typ in
    let c_repr_fixed_bytes = find_c_repr_fixed_bytes ctx.local_env typ in
    let (Typ_aux (typ_aux, l) as typ) = Env.expand_synonyms ctx.local_env typ in
    match typ_aux with
    | _ when Option.is_some c_repr_unsigned -> CT_fuint (Option.get c_repr_unsigned)
    | _ when Option.is_some c_repr_signed -> CT_fint (Option.get c_repr_signed)
    | _ when c_repr_u256 -> c_repr_u256_ctyp
    | _ when Option.is_some c_repr_fixed_bytes -> c_repr_fixed_bytes_ctyp (Option.get c_repr_fixed_bytes)
    | Typ_id id when string_of_id id = "bool" -> CT_bool
    | Typ_id id when string_of_id id = "int" -> CT_lint
    | Typ_id id when string_of_id id = "nat" -> CT_lint
    | Typ_id id when string_of_id id = "unit" -> CT_unit
    | Typ_id id when string_of_id id = "string" -> CT_string
    | Typ_id id when string_of_id id = "string_literal" -> CT_string
    | Typ_id id when string_of_id id = "real" -> CT_real
    | Typ_app (id, _) when string_of_id id = "atom_bool" -> CT_bool
    | Typ_app (id, args) when string_of_id id = "itself" -> convert_typ ctx (Typ_aux (Typ_app (mk_id "atom", args), l))
    | Typ_app (id, _) when string_of_id id = "range" || string_of_id id = "atom" || string_of_id id = "implicit" -> (
        match destruct_range Env.empty typ with
        | None -> assert false (* Checked if range type in guard *)
        | Some (kids, constr, n, m) -> (
            let ctx =
              {
                ctx with
                local_env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env;
              }
            in
            match (nexp_simp n, nexp_simp m) with
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _) when Opts.specialize_c -> (
                match smallest_native_integer_ctyp n m with
                | Some ctyp -> ctyp
                | None when Big_int.less_equal Big_int.zero n && Big_int.less_equal m (max_uint 128) -> c_repr_u128_ctyp
                | None when Big_int.less_equal (min_int 128) n && Big_int.less_equal m (max_int 128) -> CT_fint 128
                | None when Big_int.less_equal Big_int.zero n && Big_int.less_equal m (max_uint 256) -> c_repr_u256_ctyp
                | None when Big_int.less_equal Big_int.zero n && Big_int.less_equal m (max_uint 320) -> c_repr_u320_ctyp
                | None -> CT_lint
              )
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
              when Big_int.less_equal Big_int.zero n && Big_int.less_equal m (max_uint 64) ->
                CT_fuint 64
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
              when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
                CT_fint 64
            | n, m -> (
                let prove_native_integer_ctyp () =
                  if not Opts.specialize_c then None
                  else (
                    match
                      List.find_map
                        (fun width ->
                          if
                            prove __POS__ ctx.local_env (nc_lteq (nconstant Big_int.zero) n)
                            && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_uint width)))
                          then Some (CT_fuint width)
                          else None
                        )
                        native_integer_widths
                    with
                    | Some ctyp -> Some ctyp
                    | None ->
                        List.find_map
                          (fun width ->
                            if
                              prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int width)) n)
                              && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int width)))
                            then Some (CT_fint width)
                            else None
                          )
                          native_integer_widths
                  )
                in
                match prove_native_integer_ctyp () with
                | Some ctyp -> ctyp
                | None
                  when prove __POS__ ctx.local_env (nc_lteq (nconstant Big_int.zero) n)
                       && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_uint 64))) ->
                    CT_fuint 64
                | None
                  when prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n)
                       && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64))) ->
                    CT_fint 64
                | None
                  when Opts.specialize_c
                       && prove __POS__ ctx.local_env (nc_lteq (nconstant Big_int.zero) n)
                       && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_uint 128))) ->
                    c_repr_u128_ctyp
                | None
                  when Opts.specialize_c
                       && prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 128)) n)
                       && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 128))) ->
                    CT_fint 128
                | None
                  when Opts.specialize_c
                       && prove __POS__ ctx.local_env (nc_lteq (nconstant Big_int.zero) n)
                       && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_uint 256))) ->
                    c_repr_u256_ctyp
                | None
                  when Opts.specialize_c
                       && prove __POS__ ctx.local_env (nc_lteq (nconstant Big_int.zero) n)
                       && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_uint 320))) ->
                    c_repr_u320_ctyp
                | None -> CT_lint
              )
          )
      )
    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> CT_list (ctyp_suprema (convert_typ ctx typ))
    (* When converting a sail bitvector type into C, we have three options in order of efficiency:
       - If the length is obviously static and smaller than 64, use the fixed bits type (aka uint64_t), fbits.
       - If the length is less than 64, then use a small bits type, sbits.
       - If the length may be larger than 64, use a large bits type lbits. *)
    | Typ_app (id, [A_aux (A_nexp n, _)]) when string_of_id id = "bitvector" -> (
        match nexp_simp n with
        | Nexp_aux (Nexp_constant n, _) when Opts.specialize_c && Big_int.equal n (Big_int.of_int 256) ->
            (* A statically known bits(256) value has exactly the same value
               semantics as the four-limb representation used by a
               [$[c_repr u256]] newtype.  Keeping raw bridge values native is
               essential: otherwise destructuring U256, or constructing it
               again, materialises a heap-backed lbits value between two POD
               values.  This is deliberately gated by --c-specialize; other
               backends and ordinary C extraction retain the generic runtime
               representation. *)
            c_repr_u256_ctyp
        | Nexp_aux (Nexp_constant n, _) when Big_int.less_equal n (Big_int.of_int 64) -> CT_fbits (Big_int.to_int n)
        | n when prove __POS__ ctx.local_env (nc_lteq n (nint 64)) -> CT_sbits 64
        | _ -> CT_lbits
      )
    | Typ_app (id, [A_aux (A_nexp length, _); A_aux (A_typ typ, _)]) when string_of_id id = "vector" -> (
        let elem_ctyp = convert_typ ctx typ in
        match nexp_simp length with
        | Nexp_aux (Nexp_constant length, _)
          when Opts.specialize_c && ctyp_equal elem_ctyp (CT_fbits 8) && Big_int.less_equal (Big_int.of_int 1) length
          -> (
            try c_repr_fixed_bytes_ctyp (Big_int.to_int length) with _ -> CT_vector elem_ctyp
          )
        | Nexp_aux (Nexp_constant length, _)
          when Opts.specialize_c && Big_int.less_equal (Big_int.of_int 1) length -> (
            try CT_fvector (Big_int.to_int length, elem_ctyp) with _ -> CT_vector elem_ctyp
          )
        | _ -> CT_vector elem_ctyp
      )
    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "register" -> CT_ref (convert_typ ctx typ)
    | Typ_id id when Bindings.mem id ctx.records -> CT_struct (id, [])
    | Typ_app (id, typ_args) when Bindings.mem id ctx.records ->
        let ctyp_args =
          List.filter_map
            (function A_aux (A_typ typ, _) -> Some (ctyp_suprema (convert_typ ctx typ)) | _ -> None)
            typ_args
        in
        CT_struct (id, ctyp_args)
    | Typ_id id when Bindings.mem id ctx.variants -> CT_variant (id, []) |> transparent_newtype ctx
    | Typ_app (id, typ_args) when Bindings.mem id ctx.variants ->
        let ctyp_args =
          List.filter_map
            (function A_aux (A_typ typ, _) -> Some (ctyp_suprema (convert_typ ctx typ)) | _ -> None)
            typ_args
        in
        CT_variant (id, ctyp_args) |> transparent_newtype ctx
    | Typ_id id when Bindings.mem id ctx.enums -> CT_enum id
    | Typ_tuple typs -> CT_tup (List.map (convert_typ ctx) typs)
    | Typ_exist _ -> (
        (* Use Type_check.destruct_exist when optimising with SMT, to
           ensure that we don't cause any type variable clashes in
           local_env, and that we can optimize the existential based
           upon its constraints. *)
        match destruct_exist typ with
        | Some (kids, nc, typ) ->
            let env = add_existential l kids nc ctx.local_env in
            convert_typ { ctx with local_env = env } typ
        | None -> raise (Reporting.err_unreachable l __POS__ "Existential cannot be destructured!")
      )
    | Typ_var kid -> CT_poly kid
    | _ -> c_error ~loc:l ("No C type for type " ^ string_of_typ typ)

  (**************************************************************************)
  (* 3. Optimization of primitives and literals                             *)
  (**************************************************************************)

  let c_literals ctx =
    let rec c_literal annot = function
      | AV_lit (lit, typ) as v when is_stack_ctyp ctx (convert_typ { ctx with local_env = annot.env } typ) -> (
          let ctyp = convert_typ { ctx with local_env = annot.env } typ in
          match literal_to_fragment ctyp lit with Some cval -> AV_cval (cval, typ) | None -> v
        )
      | AV_tuple avals -> AV_tuple (List.map (c_literal annot) avals)
      | v -> v
    in
    map_aval c_literal

  let rec is_bitvector = function
    | [] -> true
    | AV_lit (L_aux (L_bin [Non_empty (_, [])], _), _) :: avals -> is_bitvector avals
    | _ :: _ -> false

  let value_of_aval_bit = function
    | AV_lit (L_aux (L_bin [Non_empty (b, [])], _), _) -> (
        match b with Bin_0 -> Sail2_values.B0 | Bin_1 -> Sail2_values.B1
      )
    | _ -> assert false

  (** Used to make sure the -Ofixed_int and -Ofixed_bits don't interfere with assumptions made about optimizations in
      the common case. *)
  let never_optimize = function CT_lbits | CT_lint -> true | _ -> false

  let rec c_aval ctx = function
    | AV_lit (lit, typ) as v -> (
        match literal_to_fragment (convert_typ ctx typ) lit with Some cval -> AV_cval (cval, typ) | None -> v
      )
    | AV_cval (cval, typ) -> AV_cval (cval, typ)
    (* An id can be converted to a C fragment if its type can be
       stack-allocated. *)
    | AV_id (id, lvar) as v -> (
        match lvar with
        | Local (_, typ) -> (
            let ctyp = convert_typ ctx typ in
            (* A [$[c_repr]] newtype payload retains its native representation
               after destructuring even though its semantic type is int/nat. *)
            match NameMap.find_opt id ctx.locals with
            | Some (_, represented_ctyp)
              when representation_refines ~semantic:ctyp ~represented:represented_ctyp
                   || fixed_integer_storage_compatible ~semantic:ctyp ~represented:represented_ctyp ->
                AV_cval (V_id (id, represented_ctyp), typ)
            | local ->
                if is_stack_ctyp ctx ctyp && not (never_optimize ctyp) then (
                  (* We need to check that id's type hasn't changed due to flow typing *)
                  match local with
                  | Some (_, ctyp') ->
                      if ctyp_equal ctyp ctyp' then AV_cval (V_id (id, ctyp), typ)
                      else
                        (* id's type changed due to flow typing, so it's
                          really still heap allocated! *)
                        v
                  | None -> (
                      (* We need to take special care around global
                         letbindings, to not refine their types. *)
                      match id with
                      | Name (id', _) -> (
                          match Bindings.find_opt id' ctx.letbind_ctyps with
                          | Some ctyp' -> if ctyp_equal ctyp ctyp' then AV_cval (V_id (id, ctyp), typ) else v
                          | None -> AV_cval (V_id (id, ctyp), typ)
                        )
                      | _ -> AV_cval (V_id (id, ctyp), typ)
                    )
                )
                else v
          )
        | Register typ ->
            let ctyp = convert_typ ctx typ in
            if is_stack_ctyp ctx ctyp && not (never_optimize ctyp) then AV_cval (V_id (id, ctyp), typ) else v
        | _ -> v
      )
    | AV_vector (v, typ) when is_bitvector v && List.length v <= 64 ->
        let bitstring = VL_bits (List.map value_of_aval_bit v) in
        AV_cval (V_lit (bitstring, CT_fbits (List.length v)), typ)
    | AV_tuple avals -> AV_tuple (List.map (c_aval ctx) avals)
    | aval -> aval

  let represented_aval_ctyp ctx aval =
    match c_aval ctx aval with
    | AV_cval (cval, _) -> cval_ctyp cval
    | _ -> (
        match aval with
        | AV_id (id, _) -> (
            match NameMap.find_opt id ctx.locals with Some (_, ctyp) -> ctyp | None -> convert_typ ctx (aval_typ aval)
          )
        | _ -> convert_typ ctx (aval_typ aval)
      )

  type conversion_origin = { origin_value : cval; origin_width : int }

  let conversion_origin conversion_origins value =
    match value with
    | V_id (id, _) -> (
        match NameMap.find_opt id conversion_origins with
        | Some origin -> Some origin
        | None -> (
            match cval_ctyp value with
            | CT_fbits width -> Some { origin_value = value; origin_width = width }
            | _ -> None
          )
      )
    | _ -> (
        match cval_ctyp value with
        | CT_fbits width -> Some { origin_value = value; origin_width = width }
        | _ -> None
      )

  let rec conversion_result_origin conversion_origins (AE_aux (aexp, _)) =
    (* Only immutable, conversion-only ANF chains qualify.  This restriction is
       what makes it sound to remove the chain after a proven round trip has
       replaced its final use: no effectful computation can be hidden here. *)
    match aexp with
    | AE_val (AV_cval (V_call ((Zero_extend _ | Sign_extend _), [source]), _)) ->
        conversion_origin conversion_origins source
    | AE_val (AV_cval ((V_id _ as value), _)) -> conversion_origin conversion_origins value
    | AE_typ (aexp, _) -> conversion_result_origin conversion_origins aexp
    | AE_let (mut, id, _, binding, body, _) ->
        (match (mut, conversion_result_origin conversion_origins binding) with
        | Immutable, Some origin ->
            conversion_result_origin (NameMap.add id origin conversion_origins) body
        | Mutable, _ | Immutable, None -> None)
    | _ -> None

  let aexp_uses_name id aexp =
    (* [optimize_anf] runs after [no_shadow], so equality of ANF names is enough
       to decide whether the rewritten body still refers to this binding. *)
    let used = ref false in
    let check_cval cval =
      Jib_util.map_cval
        (function
          | V_id (used_id, _) as cval when used_id = id ->
              used := true;
              cval
          | cval -> cval
          )
        cval
    in
    ignore
      (Anf.map_aval
         (fun _ -> function
           | AV_id (used_id, _) as aval when used_id = id ->
               used := true;
               aval
           | AV_cval (cval, typ) -> AV_cval (check_cval cval, typ)
           | aval -> aval
           )
         aexp
      );
    !used

  (* Map over all the functions in an aexp.  Immutable extension origins are
     retained alongside represented locals so later truncations can discharge
     round-trip identities while the semantic conversion chain is still
     explicit. *)
  let rec analyze_functions ctx conversion_origins f (AE_aux (aexp, ({ env; _ } as annot))) =
    let ctx = { ctx with local_env = env } in
    let aexp =
      match aexp with
      | AE_app (id, vs, typ) -> f ctx conversion_origins id vs typ
      | AE_typ (aexp, typ) -> AE_typ (analyze_functions ctx conversion_origins f aexp, typ)
      | AE_assign (alexp, aexp) -> AE_assign (alexp, analyze_functions ctx conversion_origins f aexp)
      | AE_short_circuit (op, aval, aexp) ->
          AE_short_circuit (op, aval, analyze_functions ctx conversion_origins f aexp)
      | AE_let (mut, id, typ1, aexp1, (AE_aux (_, { env = env2; _ }) as aexp2), typ2) ->
          let aexp1 = analyze_functions ctx conversion_origins f aexp1 in
          (* Use aexp2's environment because it will contain constraints for id *)
          let semantic_ctyp1 = convert_typ { ctx with local_env = env2 } typ1 in
          let ctyp1 =
            match (semantic_ctyp1, aexp1) with
            | semantic, AE_aux (AE_val aval, _) when mut = Immutable -> (
                match c_aval ctx aval with
                | AV_cval (cval, _) when representation_refines ~semantic ~represented:(cval_ctyp cval) ->
                    cval_ctyp cval
                | _ -> semantic
              )
            | semantic, AE_aux (AE_app (call, args, _), _) -> (
                let external_id =
                  match call with
                  | Sail_function id -> Some (if ctx_is_extern id ctx then mk_id (ctx_get_extern id ctx) else id)
                  | Pure_extern (id, _) when String.starts_with ~prefix:"__sail_proven_native_" (string_of_id id) ->
                      None
                  | Pure_extern (id, _) | Extern (id, _) -> Some id
                  | _ -> None
                in
                let arg_ctyps =
                  List.map
                    (fun arg ->
                      match c_aval ctx arg with
                      | AV_cval (cval, _) -> cval_ctyp cval
                      | arg -> convert_typ ctx (aval_typ arg)
                    )
                    args
                in
                match external_id with Some id -> specialize_call_result id arg_ctyps semantic | None -> semantic
              )
            | semantic, AE_aux (AE_field (record, field, _), { env; loc; _ }) -> (
                let field_ctx = { ctx with local_env = env } in
                match represented_aval_ctyp field_ctx record with
                | CT_struct _ as record_ctyp ->
                    let _, field_ctyp = struct_fields loc field_ctx record_ctyp in
                    let represented = field_ctyp field in
                    if representation_refines ~semantic ~represented then represented else semantic
                | _ -> semantic
              )
            | _ -> semantic_ctyp1
          in
          let ctx = { ctx with locals = NameMap.add id (mut, ctyp1) ctx.locals } in
          let binding_origin =
            match mut with
            | Immutable -> conversion_result_origin conversion_origins aexp1
            | Mutable -> None
          in
          let conversion_origins =
            match binding_origin with
            | Some origin -> NameMap.add id origin conversion_origins
            | None -> NameMap.remove id conversion_origins
          in
          let aexp2 = analyze_functions ctx conversion_origins f aexp2 in
          (match binding_origin with
          | Some _ when not (aexp_uses_name id aexp2) ->
              let AE_aux (aexp2, _) = aexp2 in
              aexp2
          | Some _ | None -> AE_let (mut, id, typ1, aexp1, aexp2, typ2))
      | AE_block (aexps, aexp, typ) ->
          AE_block
            ( List.map (analyze_functions ctx conversion_origins f) aexps,
              analyze_functions ctx conversion_origins f aexp,
              typ
            )
      | AE_if (aval, aexp1, aexp2, typ) ->
          AE_if
            ( aval,
              analyze_functions ctx conversion_origins f aexp1,
              analyze_functions ctx conversion_origins f aexp2,
              typ
            )
      | AE_loop (loop_typ, aexp1, aexp2) ->
          AE_loop
            ( loop_typ,
              analyze_functions ctx conversion_origins f aexp1,
              analyze_functions ctx conversion_origins f aexp2
            )
      | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
          let aexp1 = analyze_functions ctx conversion_origins f aexp1 in
          let aexp2 = analyze_functions ctx conversion_origins f aexp2 in
          let aexp3 = analyze_functions ctx conversion_origins f aexp3 in
          (* JIB compilation selects int64_t only after proving the complete
             loop cursor lifecycle, including the update after the last
             iteration.  Keep this earlier ANF pass representation-neutral. *)
          let ctx = { ctx with locals = NameMap.add id (Immutable, CT_lint) ctx.locals } in
          let aexp4 = analyze_functions ctx (NameMap.remove id conversion_origins) f aexp4 in
          AE_for (id, aexp1, aexp2, aexp3, order, aexp4)
      | AE_match (aval, cases, typ) ->
          let merge_pattern_bindings left right =
            NameMap.fold (fun id ctyp bindings -> NameMap.add id ctyp bindings) right left
          in
          let merge_all_pattern_bindings bindings =
            List.fold_left
              (fun merged bindings ->
                Option.bind merged (fun merged -> Option.map (merge_pattern_bindings merged) bindings)
              )
              (Some NameMap.empty) bindings
          in
          let rec represented_pattern_bindings ctyp (AP_aux (pat, { env; loc; _ })) =
            let pattern_ctx = { ctx with local_env = env } in
            let binding_ctyp typ =
              let semantic = convert_typ pattern_ctx typ in
              if representation_refines ~semantic ~represented:ctyp then ctyp else semantic
            in
            match pat with
            | AP_id (id, typ) -> (
                match id with
                | Name (id, _) when is_enum_member id env -> Some NameMap.empty
                | _ -> Some (NameMap.singleton id (binding_ctyp typ))
              )
            | AP_as (pat, id, typ) ->
                Option.map (NameMap.add id (binding_ctyp typ)) (represented_pattern_bindings ctyp pat)
            | AP_global _ | AP_nil _ | AP_wild _ -> Some NameMap.empty
            | AP_app (Newtype_wrapper _, payload, _) -> represented_pattern_bindings ctyp payload
            | AP_app (Constructor ctor, payload, _) -> (
                match ctyp with
                | CT_variant _ ->
                    let _, constructor_ctyps = variant_constructor_bindings loc pattern_ctx ctyp in
                    Option.bind (Bindings.find_opt ctor constructor_ctyps) (fun payload_ctyp ->
                        represented_pattern_bindings payload_ctyp payload
                    )
                | _ -> None
              )
            | AP_tuple pats -> (
                match ctyp with
                | CT_tup ctyps when List.compare_lengths pats ctyps = 0 ->
                    merge_all_pattern_bindings (List.map2 represented_pattern_bindings ctyps pats)
                | _ -> None
              )
            | AP_struct (fields, _) -> (
                match ctyp with
                | CT_struct _ ->
                    let _, field_ctyp = struct_fields loc pattern_ctx ctyp in
                    merge_all_pattern_bindings
                      (List.map (fun (field, pat) -> represented_pattern_bindings (field_ctyp field) pat) fields)
                | _ -> None
              )
            | AP_cons (head, tail) -> (
                match ctyp with
                | CT_list element_ctyp ->
                    merge_all_pattern_bindings
                      [represented_pattern_bindings element_ctyp head; represented_pattern_bindings ctyp tail]
                | _ -> None
              )
            | AP_vector_concat _ -> None
          in
          let represented_ctyp =
            (* Aggregate values are not themselves converted into ANF C
               fragments, but their fields can still carry specialized
               representations.  Match compilation obtains the aggregate
               type from the local JIB environment, so mirror that choice
               here when analysing the case bodies. *)
            Some (represented_aval_ctyp ctx aval)
          in
          let analyze_case ((AP_aux (_, { env; _ }) as pat), aexp1, aexp2, uannot) =
            let ctx = { ctx with local_env = env } in
            let pat_bindings =
              match represented_ctyp with
              | Some ctyp -> (
                  match represented_pattern_bindings ctyp pat with
                  | Some bindings -> NameMap.bindings bindings
                  | None -> NameMap.bindings (NameMap.map (convert_typ ctx) (apat_types pat))
                )
              | None -> NameMap.bindings (NameMap.map (convert_typ ctx) (apat_types pat))
            in
            let ctx =
              List.fold_left
                (fun ctx (id, ctyp) -> { ctx with locals = NameMap.add id (Immutable, ctyp) ctx.locals })
                ctx pat_bindings
            in
            let conversion_origins =
              List.fold_left (fun origins (id, _) -> NameMap.remove id origins) conversion_origins pat_bindings
            in
            ( pat,
              analyze_functions ctx conversion_origins f aexp1,
              analyze_functions ctx conversion_origins f aexp2,
              uannot
            )
          in
          AE_match (aval, List.map analyze_case cases, typ)
      | AE_try (aexp, cases, typ) ->
          AE_try
            ( analyze_functions ctx conversion_origins f aexp,
              List.map
                (fun (pat, aexp1, aexp2, uannot) ->
                  ( pat,
                    analyze_functions ctx conversion_origins f aexp1,
                    analyze_functions ctx conversion_origins f aexp2,
                    uannot
                  )
                )
                cases,
              typ
            )
      | (AE_field _ | AE_struct_update _ | AE_val _ | AE_return _ | AE_exit _ | AE_throw _) as v -> v
    in
    AE_aux (aexp, annot)

  let analyze_primop' ctx conversion_origins id args typ =
    let no_change = AE_app (Sail_function id, args, typ) in
    let semantic_args = args in
    let args = List.map (c_aval ctx) args in
    let extern =
      if ctx_is_extern id ctx then ctx_get_extern id ctx
      else if string_of_id id = "neq_int" then
        (* [neq_int] is the pure Sail wrapper around the external [eq_int]
           primitive.  Keeping it as a wrapper is useful to other backends,
           but represented range/newtype operands must still be compared in
           their native C type. *)
        "neq_int"
      else failwith "Not extern"
    in
    let is_fixed_integer = function CT_fint _ | CT_fuint _ -> true | _ -> false in
    let semantic_type_fits represented typ =
      try
        let typ = Env.expand_synonyms ctx.local_env typ in
        match destruct_range Env.empty typ with
        | Some (kids, constr, lower, upper) -> (
            let env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env in
            let fits lower_bound upper_bound =
              prove __POS__ env (nc_lteq lower_bound lower) && prove __POS__ env (nc_lteq upper upper_bound)
            in
            match represented with
            | CT_fuint width -> fits (nconstant Big_int.zero) (nconstant (max_uint width))
            | CT_fint width -> fits (nconstant (min_int width)) (nconstant (max_int width))
            | represented when is_c_repr_u128 represented -> fits (nconstant Big_int.zero) (nconstant (max_uint 128))
            | represented when is_c_repr_u256 represented -> fits (nconstant Big_int.zero) (nconstant (max_uint 256))
            | represented when is_c_repr_u320 represented -> fits (nconstant Big_int.zero) (nconstant (max_uint 320))
            | _ -> false
          )
        | None -> false
      with Type_error.Type_error _ -> false
    in
    let semantic_integer_fits represented = semantic_type_fits represented typ in
    let semantic_integer_value_fits represented aval = semantic_type_fits represented (aval_typ aval) in
    let semantic_integer_bounds aval =
      try
        let typ = Env.expand_synonyms ctx.local_env (aval_typ aval) in
        match destruct_range Env.empty typ with
        | Some (kids, constr, lower, upper) ->
            let env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr ctx.local_env in
            Some (env, lower, upper)
        | None -> None
      with Type_error.Type_error _ -> None
    in
    let semantic_integer_excludes value aval =
      match aval with
      | AV_lit (L_aux (L_num literal, _), _) -> not (Big_int.equal value literal)
      | AV_cval (V_lit (VL_int literal, _), _) -> not (Big_int.equal value literal)
      | _ -> (
          match semantic_integer_bounds aval with
          | Some (env, lower, upper) ->
              prove __POS__ env (nc_lt upper (nconstant value)) || prove __POS__ env (nc_lt (nconstant value) lower)
          | None -> false
        )
    in
    let semantic_integer_nonnegative aval =
      match aval with
      | AV_lit (L_aux (L_num literal, _), _) -> Big_int.less_equal Big_int.zero literal
      | AV_cval (V_lit (VL_int literal, _), _) -> Big_int.less_equal Big_int.zero literal
      | _ -> (
          match semantic_integer_bounds aval with
          | Some (env, lower, _) -> prove __POS__ env (nc_lteq (nconstant Big_int.zero) lower)
          | None -> false
        )
    in
    let semantic_division_defined represented =
      match semantic_args with
      | [left; right] -> (
          semantic_integer_excludes Big_int.zero right
          &&
          match represented with
          | CT_fint width ->
              semantic_integer_excludes (min_int width) left || semantic_integer_excludes (Big_int.of_int (-1)) right
          | CT_fuint _ -> true
          | represented when is_c_repr_u128 represented || is_c_repr_u256 represented || is_c_repr_u320 represented ->
              true
          | _ -> false
        )
      | _ -> false
    in
    let proven_native_op represented op =
      match (op, semantic_args) with
      | (Idiv | Imod), [left; right] ->
          (* Division and remainder cannot grow beyond their fixed-width
             operands.  Their only C undefined-behaviour cases are a zero
             divisor and, for signed integers, MIN / -1 (or MIN % -1).
             Prove those operand facts directly; unlike add/sub/mul, no
             independent result-range annotation is required. *)
          semantic_integer_value_fits represented left
          && semantic_integer_value_fits represented right
          && semantic_division_defined represented
      | (Idiv | Imod), _ -> false
      | (Iadd | Isub | Imul), [left; right] ->
          semantic_integer_value_fits represented left
          && semantic_integer_value_fits represented right
          && semantic_integer_fits represented
      | _ -> semantic_integer_fits represented
    in
    let proven_op = function
      | Iadd -> Proven_iadd
      | Isub -> Proven_isub
      | Imul -> Proven_imul
      | Idiv -> Proven_idiv
      | Imod -> Proven_imod
      | op -> op
    in
    let proven_marker = function
      | Iadd -> "__sail_proven_native_add"
      | Isub -> "__sail_proven_native_sub"
      | Imul -> "__sail_proven_native_mul"
      | Idiv -> "__sail_proven_native_div"
      | Imod -> "__sail_proven_native_mod"
      | _ -> assert false
    in
    let integer_literal_as ctyp = function
      | V_lit (VL_int value, _) -> (
          match ctyp with
          | CT_fuint width when Big_int.less_equal Big_int.zero value && Big_int.less_equal value (max_uint width) ->
              Some (V_lit (VL_int value, ctyp))
          | CT_fint width when Big_int.less_equal (min_int width) value && Big_int.less_equal value (max_int width) ->
              Some (V_lit (VL_int value, ctyp))
          | _ -> None
        )
      | _ -> None
    in
    let align_fixed_integers left right =
      let left_ctyp = cval_ctyp left in
      let right_ctyp = cval_ctyp right in
      if is_fixed_integer left_ctyp && ctyp_equal left_ctyp right_ctyp then Some (left, right)
      else (
        match
          if is_fixed_integer left_ctyp then Option.map (fun right -> (left, right)) (integer_literal_as left_ctyp right)
          else None
        with
        | Some aligned -> Some aligned
        | None ->
            if is_fixed_integer right_ctyp then
              Option.map (fun left -> (left, right)) (integer_literal_as right_ctyp left)
            else None
      )
    in
    let native_binary op left right =
      let exact_mixed_fixed_comparison =
        let comparison = match op with Eq | Neq | Ilt | Igt | Ilteq | Igteq -> true | _ -> false in
        let exact_c_conversion left right =
          match (left, right) with
          | CT_fint left_width, CT_fint right_width -> left_width <> right_width
          | CT_fuint left_width, CT_fuint right_width -> left_width <> right_width
          | CT_fint signed_width, CT_fuint unsigned_width | CT_fuint unsigned_width, CT_fint signed_width ->
              signed_width > unsigned_width
          | _ -> false
        in
        comparison && exact_c_conversion (cval_ctyp left) (cval_ctyp right)
      in
      if exact_mixed_fixed_comparison then
        (* The usual C arithmetic conversion is exact when both operands have
           the same signedness, or when the signed carrier is strictly wider
           than the unsigned carrier.  Keep both proven source
           representations and compare them directly instead of routing
           through Sail's arbitrary-precision integer runtime. *)
        Some (AE_val (AV_cval (V_call (op, [left; right]), typ)))
      else
        Option.bind (align_fixed_integers left right) (fun (left, right) ->
            let represented = cval_ctyp left in
            let operation_fits =
              match op with
              | Eq | Neq | Ilt | Igt | Ilteq | Igteq -> true
              | Iadd | Isub | Imul | Idiv | Imod -> proven_native_op represented op
              | _ -> false
            in
            if operation_fits then Some (AE_val (AV_cval (V_call (proven_op op, [left; right]), typ))) else None
        )
    in
    let native_binary_or_no_change op left right = Option.value (native_binary op left right) ~default:no_change in
    let as_native_u64 = function
      | value when match cval_ctyp value with CT_fuint _ -> true | _ -> false -> Some value
      | V_lit (VL_int value, _) when Big_int.less_equal Big_int.zero value && Big_int.less_equal value (max_uint 64) ->
          Some (V_lit (VL_int value, CT_fuint 64))
      | _ -> None
    in
    let align_u320_integers left right =
      let left_ctyp = cval_ctyp left in
      let right_ctyp = cval_ctyp right in
      match (is_c_repr_u320 left_ctyp, is_c_repr_u320 right_ctyp) with
      | true, true -> Some (left, right)
      | true, false when is_c_repr_u128 right_ctyp || is_c_repr_u256 right_ctyp -> Some (left, right)
      | false, true when is_c_repr_u128 left_ctyp || is_c_repr_u256 left_ctyp -> Some (left, right)
      | true, false -> Option.map (fun right -> (left, right)) (as_native_u64 right)
      | false, true -> Option.map (fun left -> (left, right)) (as_native_u64 left)
      | false, false -> None
    in
    let align_u256_integers left right =
      let left_ctyp = cval_ctyp left in
      let right_ctyp = cval_ctyp right in
      match (is_c_repr_u256 left_ctyp, is_c_repr_u256 right_ctyp) with
      | true, true -> Some (left, right)
      | true, false when is_c_repr_u128 right_ctyp -> Some (left, right)
      | false, true when is_c_repr_u128 left_ctyp -> Some (left, right)
      | true, false -> Option.map (fun right -> (left, right)) (as_native_u64 right)
      | false, true -> Option.map (fun left -> (left, right)) (as_native_u64 left)
      | false, false -> None
    in
    let align_u128_integers left right =
      match (is_c_repr_u128 (cval_ctyp left), is_c_repr_u128 (cval_ctyp right)) with
      | true, true -> Some (left, right)
      | true, false -> Option.map (fun right -> (left, right)) (as_native_u64 right)
      | false, true -> Option.map (fun left -> (left, right)) (as_native_u64 left)
      | false, false -> None
    in
    let widening_u128_binary op left right =
      let widening_op =
        match op with
        | Iadd -> Some (Widening_iadd (128, convert_typ ctx typ))
        | Imul -> Some (Widening_imul (128, convert_typ ctx typ))
        | _ -> None
      in
      match (widening_op, as_native_u64 left, as_native_u64 right) with
      | Some op, Some left, Some right -> Some (AE_val (AV_cval (V_call (op, [left; right]), typ)))
      | _ -> None
    in
    let widening_u256_binary op left right =
      let supported_operands =
        match (cval_ctyp left, cval_ctyp right) with
        | left, right when is_c_repr_u128 left && is_c_repr_u128 right -> true
        | left, CT_fuint _ when is_c_repr_u128 left -> true
        | CT_fuint _, right when is_c_repr_u128 right -> true
        | _ -> false
      in
      let widening_op =
        match op with
        | Iadd -> Some (Widening_iadd (256, convert_typ ctx typ))
        | Imul -> Some (Widening_imul (256, convert_typ ctx typ))
        | _ -> None
      in
      match widening_op with
      | Some op when supported_operands -> Some (AE_val (AV_cval (V_call (op, [left; right]), typ)))
      | _ -> None
    in
    let widening_u320_binary op left right =
      let widening_op =
        match op with
        | Iadd -> Some (Widening_iadd (320, convert_typ ctx typ))
        | Imul -> Some (Widening_imul (320, convert_typ ctx typ))
        | _ -> None
      in
      match widening_op with
      | Some op
        when match (cval_ctyp left, cval_ctyp right) with
             | left, right ->
                 (is_c_repr_u320 left || is_c_repr_u256 left || is_c_repr_u128 left
                 || match left with CT_fuint _ -> true | _ -> false
                 )
                 && (is_c_repr_u320 right || is_c_repr_u256 right || is_c_repr_u128 right
                    || match right with CT_fuint _ -> true | _ -> false
                    ) ->
          Some (AE_val (AV_cval (V_call (op, [left; right]), typ)))
      | _ -> None
    in
    let native_integer_binary_or_no_change ?(commutative = false) op left right =
      let native_operation left right =
        match op with
        | Iadd | Isub | Imul ->
            let semantic_typ index = aval_typ (List.nth semantic_args index) in
            AE_app
              ( Pure_extern (mk_id (proven_marker op), Some typ),
                [AV_cval (left, semantic_typ 0); AV_cval (right, semantic_typ 1)],
                typ
              )
        | _ -> AE_val (AV_cval (V_call (op, [left; right]), typ))
      in
      let operation_fits represented =
        match op with
        | Eq | Neq | Ilt | Igt | Ilteq | Igteq -> true
        | (Iadd | Isub | Imul | Idiv | Imod) when is_c_repr_u320 represented -> is_c_repr_u320 (convert_typ ctx typ)
        | Iadd | Isub | Imul | Idiv | Imod -> proven_native_op represented op
        | _ -> false
      in
      match if is_c_repr_u320 (convert_typ ctx typ) then widening_u320_binary op left right else None with
      | Some widened -> widened
      | None -> (
          match align_u320_integers left right with
          | Some (left, right)
            when match op with Idiv | Imod -> is_c_repr_u320 (cval_ctyp left) | _ -> operation_fits c_repr_u320_ctyp ->
              let left, right =
                if commutative && not (is_c_repr_u320 (cval_ctyp left)) then (right, left) else (left, right)
              in
              if op = Imod && match cval_ctyp right with CT_fuint _ -> true | _ -> false then (
                let semantic_typ index = aval_typ (List.nth semantic_args index) in
                AE_app
                  ( Pure_extern (mk_id "u320_mod_u64", Some typ),
                    [AV_cval (left, semantic_typ 0); AV_cval (right, semantic_typ 1)],
                    typ
                  )
              )
              else native_operation left right
          | Some _ | None -> (
              match if is_c_repr_u256 (convert_typ ctx typ) then widening_u256_binary op left right else None with
              | Some widened -> widened
              | None -> (
                  match align_u256_integers left right with
                  | Some (left, right) when operation_fits c_repr_u256_ctyp ->
                      let left, right =
                        if commutative && not (is_c_repr_u256 (cval_ctyp left)) then (right, left) else (left, right)
                      in
                      native_operation left right
                  | Some _ | None -> (
                      match align_u128_integers left right with
                      | Some (left, right) when operation_fits c_repr_u128_ctyp ->
                          let left, right =
                            if commutative && not (is_c_repr_u128 (cval_ctyp left)) then (right, left) else (left, right)
                          in
                          native_operation left right
                      | (Some _ | None) when is_c_repr_u128 (convert_typ ctx typ) ->
                          Option.value (widening_u128_binary op left right) ~default:no_change
                      | Some _ | None -> native_binary_or_no_change op left right
                    )
                )
            )
        )
    in
    let native_shift_amount = function
      | V_lit (VL_int value, _) when Big_int.less_equal Big_int.zero value && Big_int.less_equal value (max_uint 64) ->
          Some (V_lit (VL_int value, CT_fuint 64))
      | amount when is_fixed_integer (cval_ctyp amount) -> Some amount
      | _ -> None
    in

    match (extern, args) with
    | "neg_int", [AV_cval (V_lit (VL_int value, _), _)] -> (
        match convert_typ ctx typ with
        | CT_fint _ as result_ctyp -> (
            match integer_literal_as result_ctyp (V_lit (VL_int (Big_int.negate value), result_ctyp)) with
            | Some result -> AE_val (AV_cval (result, typ))
            | None -> no_change
          )
        | _ -> no_change
      )
    | "eq_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) -> (
        match cval_ctyp v1 with
        | CT_fbits _ | CT_sbits _ -> AE_val (AV_cval (V_call (Eq, [v1; v2]), typ))
        | ctyp when is_c_repr_u256 ctyp -> AE_val (AV_cval (V_call (Eq, [v1; v2]), typ))
        | _ -> no_change
      )
    | "neq_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) -> (
        match cval_ctyp v1 with
        | CT_fbits _ | CT_sbits _ -> AE_val (AV_cval (V_call (Neq, [v1; v2]), typ))
        | ctyp when is_c_repr_u256 ctyp -> AE_val (AV_cval (V_call (Neq, [v1; v2]), typ))
        | _ -> no_change
      )
    | "eq_int", [AV_cval (v1, _); AV_cval (v2, _)] -> native_integer_binary_or_no_change Eq v1 v2
    | "neq_int", [AV_cval (v1, _); AV_cval (v2, _)] -> native_integer_binary_or_no_change Neq v1 v2
    | "eq_bit", [AV_cval (v1, _); AV_cval (v2, _)] -> AE_val (AV_cval (V_call (Eq, [v1; v2]), typ))
    | "zeros", [_] -> (
        match destruct_bitvector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) when Big_int.less_equal n (Big_int.of_int 64) ->
            let n = Big_int.to_int n in
            AE_val (AV_cval (V_lit (VL_bits (Util.list_init n (fun _ -> Sail2_values.B0)), CT_fbits n), typ))
        | _ -> no_change
      )
    | "zero_extend", [AV_cval (v, _); _] -> (
        let source_typ = aval_typ (List.hd semantic_args) in
        match (destruct_bitvector ctx.local_env source_typ, destruct_bitvector ctx.local_env typ) with
        | ( Some (Nexp_aux (Nexp_constant source_width, _)),
            Some (Nexp_aux (Nexp_constant target_width, _)) )
          when Big_int.less_equal source_width (Big_int.of_int 64)
               && Big_int.less_equal target_width (Big_int.of_int 64) -> (
            let source_width = Big_int.to_int source_width in
            let target_width = Big_int.to_int target_width in
            match Jib_semantics.prove_conversion_value_preserving ~source_width ~target_width with
            | Some _ when source_width = target_width -> AE_val (AV_cval (v, typ))
            | Some _ -> AE_val (AV_cval (V_call (Zero_extend target_width, [v]), typ))
            | None -> no_change
          )
        | _ -> no_change
      )
    | "sign_extend", [AV_cval (v, _); _] -> (
        let source_typ = aval_typ (List.hd semantic_args) in
        match (destruct_bitvector ctx.local_env source_typ, destruct_bitvector ctx.local_env typ) with
        | ( Some (Nexp_aux (Nexp_constant source_width, _)),
            Some (Nexp_aux (Nexp_constant target_width, _)) )
          when Big_int.less_equal source_width (Big_int.of_int 64)
               && Big_int.less_equal target_width (Big_int.of_int 64) -> (
            let source_width = Big_int.to_int source_width in
            let target_width = Big_int.to_int target_width in
            match Jib_semantics.prove_signed_conversion_value_preserving ~source_width ~target_width with
            | Some _ when source_width = target_width -> AE_val (AV_cval (v, typ))
            | Some _ -> AE_val (AV_cval (V_call (Sign_extend target_width, [v]), typ))
            | None -> no_change
          )
        | _ -> no_change
      )
    | "sail_truncate", [AV_cval (v, _); _] -> (
        let source_typ = aval_typ (List.hd semantic_args) in
        match (destruct_bitvector ctx.local_env source_typ, destruct_bitvector ctx.local_env typ) with
        | ( Some (Nexp_aux (Nexp_constant source_width, _)),
            Some (Nexp_aux (Nexp_constant target_width, _)) )
          when Big_int.less_equal source_width (Big_int.of_int 64)
               && Big_int.less_equal target_width (Big_int.of_int 64) -> (
            let source_width = Big_int.to_int source_width in
            let target_width = Big_int.to_int target_width in
            match Jib_semantics.prove_conversion_low_bits ~source_width ~target_width with
            | Some _ when source_width = target_width -> AE_val (AV_cval (v, typ))
            | Some _ -> (
                match conversion_origin conversion_origins v with
                | Some { origin_value; origin_width } when origin_width = target_width ->
                    AE_val (AV_cval (origin_value, typ))
                | Some _ | None ->
                    let start = V_lit (VL_int Big_int.zero, CT_fuint 64) in
                    AE_val (AV_cval (V_call (Slice target_width, [v; start]), typ))
              )
            | None -> no_change
          )
        | _ -> no_change
      )
    | "lteq", [AV_cval (v1, _); AV_cval (v2, _)] -> native_integer_binary_or_no_change Ilteq v1 v2
    | "gteq", [AV_cval (v1, _); AV_cval (v2, _)] -> native_integer_binary_or_no_change Igteq v1 v2
    | "lt", [AV_cval (v1, _); AV_cval (v2, _)] -> native_integer_binary_or_no_change Ilt v1 v2
    | "gt", [AV_cval (v1, _); AV_cval (v2, _)] -> native_integer_binary_or_no_change Igt v1 v2
    | "append", [AV_cval (v1, _); AV_cval (v2, _)] -> (
        match convert_typ ctx typ with
        | CT_fbits _ | CT_sbits _ -> AE_val (AV_cval (V_call (Concat, [v1; v2]), typ))
        | _ -> no_change
      )
    | "not_bits", [AV_cval (v, _)] -> AE_val (AV_cval (V_call (Bvnot, [v]), typ))
    | "add_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvadd, [v1; v2]), typ))
    | "sub_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvsub, [v1; v2]), typ))
    | "and_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvand, [v1; v2]), typ))
    | "or_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvor, [v1; v2]), typ))
    | "xor_bits", [AV_cval (v1, _); AV_cval (v2, _)] when ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Bvxor, [v1; v2]), typ))
    | (("shiftl" | "shiftr" | "arith_shiftr") as shift), [AV_cval (value, _); AV_cval (amount, _)] -> (
        let count_is_proven =
          match semantic_args with
          | [_; semantic_amount] -> (
              match
                Jib_semantics.prove_shift_count_bounds ~env:ctx.local_env ~index:1 ~typ:(aval_typ semantic_amount)
                  ~interval:None ~carrier_width:64
              with
              | Some proof -> Jib_semantics.has_shift_count_bounds ~index:1 ~carrier_width:64 [proof]
              | None -> false
            )
          | _ -> false
        in
        match (cval_ctyp value, native_shift_amount amount) with
        | CT_fbits 0, Some _ when shift = "arith_shiftr" -> no_change
        | CT_fbits _, Some amount ->
            let op =
              match (shift, count_is_proven) with
              | "shiftl", true -> Proven_bvshiftl 64
              | "shiftr", true -> Proven_bvshiftr 64
              | "shiftl", false -> Bvshiftl
              | "shiftr", false -> Bvshiftr
              | "arith_shiftr", true -> Proven_bvarith_shiftr 64
              | "arith_shiftr", false -> Bvarith_shiftr
              | _ -> assert false
            in
            AE_val (AV_cval (V_call (op, [value; amount]), typ))
        | _ -> no_change
      )
    | "sail_unsigned", [AV_cval (value, _)] -> (
        match cval_ctyp value with
        | CT_fbits _ -> AE_val (AV_cval (V_call (Unsigned 64, [value]), typ))
        | ctyp when is_c_repr_u320 ctyp -> AE_val (AV_cval (value, typ))
        | ctyp when is_c_repr_u256 ctyp -> AE_val (AV_cval (value, typ))
        | _ -> no_change
      )
    | "sail_signed", [AV_cval (value, _)] -> (
        match cval_ctyp value with CT_fbits _ -> AE_val (AV_cval (V_call (Signed 64, [value]), typ)) | _ -> no_change
      )
    | "vector_subrange", [AV_cval (vec, _); AV_cval (_, _); AV_cval (t, _)] -> (
        match convert_typ ctx typ with
        | CT_fbits n -> AE_val (AV_cval (V_call (Slice n, [vec; t]), typ))
        | _ -> no_change
      )
    | "slice", [AV_cval (vec, _); AV_cval (start, _); AV_cval (len, _)] -> (
        match convert_typ ctx typ with
        | CT_fbits n -> AE_val (AV_cval (V_call (Slice n, [vec; start]), typ))
        | CT_sbits 64 -> AE_val (AV_cval (V_call (Sslice 64, [vec; start; len]), typ))
        | _ -> no_change
      )
    | "set_slice", [_; _; AV_cval (vec, _); AV_cval (start, _); AV_cval (slice, _)] -> (
        match (convert_typ ctx typ, cval_ctyp vec, cval_ctyp slice) with
        | CT_fbits result_width, CT_fbits source_width, CT_fbits slice_width
          when result_width = source_width -> (
            let position_is_proven =
              match semantic_args with
              | [_; _; _; semantic_start; _] ->
                  Option.is_some
                    (Jib_semantics.prove_bit_insert_position_bounds ~env:ctx.local_env ~index:3
                       ~typ:(aval_typ semantic_start) ~interval:None ~carrier_width:result_width
                       ~inserted_width:slice_width)
              | _ -> false
            in
            match (position_is_proven, native_shift_amount start) with
            | true, Some start ->
                (* The semantic position proof makes both native shifts
                   defined and keeps the inserted value inside the carrier.
                   Preserve Set_slice as a structural JIB operation so its
                   result bound can flow through the definition/call graph. *)
                AE_val (AV_cval (V_call (Set_slice, [vec; start; slice]), typ))
            | false, _ | _, None -> no_change
          )
        | _ -> no_change
      )
    | "get_slice_int", [AV_cval (V_lit (VL_int width, _), _); AV_cval (value, _); AV_cval (V_lit (VL_int start, _), _)]
      when Big_int.equal width (Big_int.of_int 256)
           && Big_int.equal start Big_int.zero
           && is_c_repr_u256 (cval_ctyp value) ->
        AE_val (AV_cval (value, typ))
    | "get_slice_int", [AV_cval (V_lit (VL_int width, _), _); AV_cval (value, _); AV_cval (V_lit (VL_int start, _), _)]
      when Big_int.less (Big_int.of_int 64) width
           && Big_int.less_equal width (Big_int.of_int 256)
           && Big_int.equal start Big_int.zero
           && is_c_repr_u256 (cval_ctyp value)
           && ctyp_equal (convert_typ ctx typ) CT_lbits ->
        let mask =
          V_lit (VL_bits (Util.list_init (Big_int.to_int width) (fun _ -> Sail2_values.B1)), c_repr_u256_ctyp)
        in
        AE_val (AV_cval (V_call (Bvand, [value; mask]), typ))
    | "get_slice_int", [_; AV_cval (value, _); AV_cval (start, _)] -> (
        match (convert_typ ctx typ, cval_ctyp value, native_shift_amount start) with
        | CT_fbits n, ctyp, Some start when n <= 64 && is_c_repr_u256 ctyp ->
            (* A fixed-width slice of a u256 fits in one native limb.  Lower
               it directly instead of materialising the semantic lbits
               result used by get_slice_int's generic implementation. *)
            AE_val (AV_cval (V_call (Slice n, [value; start]), typ))
        | CT_fbits n, CT_fuint _, Some start when n <= 64 ->
            (* A non-negative bounded integer already has the same low-bit
               encoding as its uint64_t representation.  Keep this common
               nat/range -> bits bridge native instead of materialising a
               GMP integer merely to extract at most one limb. *)
            AE_val (AV_cval (V_call (Slice n, [value; start]), typ))
        | _ -> no_change
      )
    | "vector_access", [AV_cval (vec, _); AV_cval (n, _)]
      when match cval_ctyp vec with CT_fbits _ | CT_sbits _ -> true | ctyp -> is_c_repr_u256 ctyp ->
        AE_val (AV_cval (V_call (Bvaccess, [vec; n]), typ))
    | "vector_access", [v; AV_cval (n, _)] -> (
        match destruct_vector ctx.tc_env (aval_typ v) with
        | Some (_, elem_typ) -> (
            match cval_ctyp n with
            | CT_fint width when width <= 64 ->
                AE_app (Pure_extern (mk_id "fast_vector_access", Some elem_typ), args, typ)
            | CT_fuint width when width <= 64 ->
                AE_app (Pure_extern (mk_id "fast_unsigned_vector_access", Some elem_typ), args, typ)
            | _ -> no_change
          )
        | None -> no_change
      )
    | (("add_int" | "sub_int" | "mult_int" | "tdiv_int" | "tmod_int") as f), [AV_cval (op1, _); AV_cval (op2, _)] ->
        let op =
          match f with
          | "add_int" -> Iadd
          | "sub_int" -> Isub
          | "mult_int" -> Imul
          | "tdiv_int" -> Idiv
          | "tmod_int" -> Imod
          | _ -> assert false
        in
        let result_representation = convert_typ ctx typ in
        let proven_fixed_result =
          match result_representation with
          | (CT_fuint width | CT_fint width) as represented -> width <= 128 && proven_native_op represented op
          | _ -> false
        in
        if proven_fixed_result then
          (* Preserve the source-level operand/result range proof until JIB
             lowering sees the concrete destination.  It then promotes both
             operands before performing the operation, so the selected type
             covers the complete arithmetic-result lifetime. *)
          AE_app (Pure_extern (mk_id (proven_marker op), Some typ), args, typ)
        else if ctyp_equal result_representation CT_lint then no_change
        else native_integer_binary_or_no_change ~commutative:(f = "add_int" || f = "mult_int") op op1 op2
    | ("mult_vec" | "mults_vec"), [AV_cval (op1, _); AV_cval (op2, _)]
      when is_c_repr_u256 (cval_ctyp op1) && ctyp_equal (cval_ctyp op1) (cval_ctyp op2) ->
        (* Both operations agree modulo 2^256 when the result width is 256.
           The backend helper computes exactly those low four limbs. *)
        AE_val (AV_cval (V_call (Imul, [op1; op2]), typ))
    | "ediv_int", [AV_cval (op1, _); AV_cval (op2, _)] -> (
        let represented = convert_typ ctx typ in
        match semantic_args with
        | [left; right]
          when semantic_integer_nonnegative left
               && semantic_integer_nonnegative right
               && proven_native_op represented Idiv ->
            (* Euclidean and truncating division coincide for non-negative
               operands.  Emit the proof-bearing marker while the source
               environment still knows that the divisor is non-zero (for
               example after a terminating zero guard); later graph
               specialization can then keep the operation native. *)
            AE_app (Pure_extern (mk_id (proven_marker Idiv), Some typ), args, typ)
        | _ -> native_integer_binary_or_no_change Idiv op1 op2
      )
    | "emod_int", [AV_cval (op1, _); AV_cval (op2, _)] ->
        let nonnegative_dividend =
          match cval_ctyp op1 with
          | CT_fuint _ -> true
          | ctyp when is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp -> true
          | CT_constant value -> Big_int.less_equal Big_int.zero value
          | _ -> false
        in
        let represented = convert_typ ctx typ in
        (match semantic_args with
        | [left; right]
          when semantic_integer_nonnegative left
               && semantic_integer_nonnegative right
               && proven_native_op represented Imod ->
            AE_app (Pure_extern (mk_id (proven_marker Imod), Some typ), args, typ)
        | _ -> if nonnegative_dividend then native_integer_binary_or_no_change Imod op1 op2 else no_change)
    | "replicate_bits", [AV_cval (vec, vtyp); _] -> (
        match (destruct_vector ctx.tc_env typ, destruct_vector ctx.tc_env vtyp) with
        | Some (Nexp_aux (Nexp_constant n, _), _), Some (Nexp_aux (Nexp_constant m, _), _)
          when Big_int.less_equal n (Big_int.of_int 64) ->
            let times = Big_int.div n m in
            if Big_int.equal (Big_int.mul m times) n then
              AE_val (AV_cval (V_call (Replicate (Big_int.to_int times), [vec]), typ))
            else no_change
        | _, _ -> no_change
      )
    | "print_int", [_; AV_cval (value, _)]
      when match cval_ctyp value with CT_fint _ | CT_constant _ -> true | _ -> false ->
        AE_app (Extern (mk_id "fast_print_int", None), args, typ)
    | "undefined_bit", _ -> AE_val (AV_cval (V_lit (VL_bits [Sail2_values.B0], CT_fbits 1), typ))
    | "undefined_bool", _ -> AE_val (AV_cval (V_lit (VL_bool false, CT_bool), typ))
    | _, _ -> no_change

  let analyze_primop ctx conversion_origins id args typ =
    let no_change = AE_app (id, args, typ) in
    match id with
    | Sail_function id ->
        if !optimize_primops then
          (try analyze_primop' ctx conversion_origins id args typ with Failure _ -> no_change)
        else no_change
    | _ -> no_change

  let optimize_anf ctx aexp = analyze_functions ctx NameMap.empty analyze_primop (c_literals ctx aexp)

  let unroll_loops = None
  let make_call_precise _ _ _ _ = true
  let ignore_64 = false
  let struct_value = false
  let tuple_value = false
  let use_real = false
  let branch_coverage = Opts.branch_coverage
  let track_throw = not Opts.optimized_model
  let assert_to_exception = Opts.assert_to_exception
  let erase_assert_messages = Opts.optimized_model
  let use_void = false
  let eager_control_flow = false
  let preserve_types = Opts.preserve_types
  let fun_to_wires = Bindings.empty
end

(** Functions that have heap-allocated return types are implemented by passing a pointer a location where the return
    value should be stored. The ANF -> Sail IR pass for expressions simply outputs an I_return instruction for any
    return value, so this function walks over the IR ast for expressions and modifies the return statements into code
    that sets that pointer, as well as adds extra control flow to cleanup heap-allocated variables correctly when a
    function terminates early. See the generate_cleanup function for how this is done. *)
let fix_early_heap_return ret instrs =
  let end_function_label = label "end_function_" in
  let is_return_recur (I_aux (instr, _)) =
    match instr with
    | I_if _ | I_block _ | I_try_block _ | I_end _ | I_funcall _ | I_copy _ | I_undefined _ -> true
    | _ -> false
  in
  let rec rewrite_return instrs =
    match instr_split_at is_return_recur instrs with
    | instrs, [] -> instrs
    | before, I_aux (I_block instrs, _) :: after -> before @ [iblock (rewrite_return instrs)] @ rewrite_return after
    | before, I_aux (I_try_block instrs, (_, l)) :: after ->
        before @ [itry_block l (rewrite_return instrs)] @ rewrite_return after
    | before, I_aux (I_if (cval, then_instrs, else_instrs), (_, l)) :: after ->
        before @ [iif l cval (rewrite_return then_instrs) (rewrite_return else_instrs)] @ rewrite_return after
    | before, I_aux (I_funcall (CR_one (CL_id (Return _, ctyp)), extern, fid, args), aux) :: after ->
        before
        @ [I_aux (I_funcall (CR_one (CL_addr (CL_id (ret, CT_ref ctyp))), extern, fid, args), aux)]
        @ rewrite_return after
    | before, I_aux (I_copy (CL_id (Return _, ctyp), cval), aux) :: after ->
        before @ [I_aux (I_copy (CL_addr (CL_id (ret, CT_ref ctyp)), cval), aux)] @ rewrite_return after
    | before, I_aux ((I_end _ | I_undefined _), _) :: after ->
        before @ [igoto end_function_label] @ rewrite_return after
    | before, (I_aux ((I_copy _ | I_funcall _), _) as instr) :: after -> before @ (instr :: rewrite_return after)
    | _, _ -> assert false
  in
  rewrite_return instrs @ [ilabel end_function_label]

(* This is like fix_early_heap_return, but for stack allocated returns. *)
let fix_early_stack_return ret ret_ctyp instrs =
  let is_return_recur (I_aux (instr, _)) =
    match instr with I_if _ | I_block _ | I_try_block _ | I_end _ | I_funcall _ | I_copy _ -> true | _ -> false
  in
  let rec rewrite_return instrs =
    match instr_split_at is_return_recur instrs with
    | instrs, [] -> instrs
    | before, I_aux (I_block instrs, _) :: after -> before @ [iblock (rewrite_return instrs)] @ rewrite_return after
    | before, I_aux (I_try_block instrs, (_, l)) :: after ->
        before @ [itry_block l (rewrite_return instrs)] @ rewrite_return after
    | before, I_aux (I_if (cval, then_instrs, else_instrs), (_, l)) :: after ->
        before @ [iif l cval (rewrite_return then_instrs) (rewrite_return else_instrs)] @ rewrite_return after
    | before, I_aux (I_funcall (CR_one (CL_id (Return _, ctyp)), extern, fid, args), aux) :: after ->
        before @ [I_aux (I_funcall (CR_one (CL_id (ret, ctyp)), extern, fid, args), aux)] @ rewrite_return after
    | before, I_aux (I_copy (CL_id (Return _, ctyp), cval), aux) :: after ->
        before @ [I_aux (I_copy (CL_id (ret, ctyp), cval), aux)] @ rewrite_return after
    | before, I_aux (I_end _, _) :: after -> before @ [ireturn (V_id (ret, ret_ctyp))] @ rewrite_return after
    | before, (I_aux ((I_copy _ | I_funcall _), _) as instr) :: after -> before @ (instr :: rewrite_return after)
    | _, _ -> assert false
  in
  rewrite_return instrs

let rec insert_heap_returns ctx ret_ctyps = function
  | (CDEF_aux (CDEF_val (id, _, _, ret_ctyp, _), _) as cdef) :: cdefs ->
      cdef :: insert_heap_returns ctx (Bindings.add id ret_ctyp ret_ctyps) cdefs
  | CDEF_aux (CDEF_fundef (id, Return_plain, args, body), def_annot) :: cdefs -> (
      match Bindings.find_opt id ret_ctyps with
      | None -> raise (Reporting.err_general (id_loc id) ("Cannot find return type for function " ^ string_of_id id))
      | Some ret_ctyp when not (is_stack_ctyp ctx ret_ctyp) ->
          let gs = ngensym ~source_name:"result" ~source_type:(string_of_ctyp ret_ctyp) () in
          CDEF_aux (CDEF_fundef (id, Return_via gs, args, fix_early_heap_return gs body), def_annot)
          :: insert_heap_returns ctx ret_ctyps cdefs
      | Some ret_ctyp ->
          let gs = ngensym ~source_name:"result" ~source_type:(string_of_ctyp ret_ctyp) () in
          CDEF_aux
            ( CDEF_fundef
                (id, Return_plain, args, fix_early_stack_return gs ret_ctyp (idecl (id_loc id) ret_ctyp gs :: body)),
              def_annot
            )
          :: insert_heap_returns ctx ret_ctyps cdefs
    )
  | CDEF_aux (CDEF_fundef (id, _, _, _), _) :: _ ->
      Reporting.unreachable (id_loc id) __POS__ "Found function with return already re-written in insert_heap_returns"
  | cdef :: cdefs -> cdef :: insert_heap_returns ctx ret_ctyps cdefs
  | [] -> []

(**************************************************************************)
(* 5. Optimizations                                                       *)
(**************************************************************************)

let hoist_ctyp = function CT_lint | CT_lbits | CT_struct _ -> true | _ -> false

let hoist_counter = ref 0
let hoist_id () =
  let id = mk_id ("gh#" ^ string_of_int !hoist_counter) in
  incr hoist_counter;
  name id

let hoist_allocations recursive_functions = function
  | CDEF_aux (CDEF_fundef (function_id, _, _, _), _) as cdef when IdSet.mem function_id recursive_functions -> [cdef]
  | CDEF_aux (CDEF_fundef (function_id, heap_return, args, body), def_annot) ->
      let decls = ref [] in
      let cleanups = ref [] in
      let rec hoist = function
        | I_aux (I_decl (ctyp, decl_id), annot) :: instrs when hoist_ctyp ctyp ->
            let hid = hoist_id () in
            decls := idecl (snd annot) ctyp hid :: !decls;
            cleanups := iclear ctyp hid :: !cleanups;
            let instrs = instrs_rename decl_id hid instrs in
            I_aux (I_reset (ctyp, hid), annot) :: hoist instrs
        | I_aux (I_init (ctyp, decl_id, Init_cval cval), annot) :: instrs when hoist_ctyp ctyp ->
            let hid = hoist_id () in
            decls := idecl (snd annot) ctyp hid :: !decls;
            cleanups := iclear ctyp hid :: !cleanups;
            let instrs = instrs_rename decl_id hid instrs in
            I_aux (I_reinit (ctyp, hid, cval), annot) :: hoist instrs
        | I_aux (I_clear (ctyp, _), _) :: instrs when hoist_ctyp ctyp -> hoist instrs
        | I_aux (I_block block, annot) :: instrs -> I_aux (I_block (hoist block), annot) :: hoist instrs
        | I_aux (I_try_block block, annot) :: instrs -> I_aux (I_try_block (hoist block), annot) :: hoist instrs
        | I_aux (I_if (cval, then_instrs, else_instrs), annot) :: instrs ->
            I_aux (I_if (cval, hoist then_instrs, hoist else_instrs), annot) :: hoist instrs
        | instr :: instrs -> instr :: hoist instrs
        | [] -> []
      in
      let body = hoist body in
      if !decls = [] then [CDEF_aux (CDEF_fundef (function_id, heap_return, args, body), def_annot)]
      else
        [
          CDEF_aux (CDEF_startup (function_id, List.rev !decls), mk_def_annot (gen_loc def_annot.loc) ());
          CDEF_aux (CDEF_fundef (function_id, heap_return, args, body), def_annot);
          CDEF_aux (CDEF_finish (function_id, !cleanups), mk_def_annot (gen_loc def_annot.loc) ());
        ]
  | cdef -> [cdef]

let removed = icomment "REMOVED"

let is_not_removed = function I_aux (I_comment "REMOVED", _) -> false | _ -> true

(** This optimization looks for patterns of the form:

    {v
       create x : t;
       x = y;
       // modifications to x, and no changes to y
       y = x;
       // no further changes to x
       kill x;
    v}

    If found, we can remove the variable x, and directly modify y instead. *)
let remove_alias =
  let pattern ctyp id =
    let alias = ref None in
    let rec scan ctyp id n instrs =
      match (n, !alias, instrs) with
      | 0, None, I_aux (I_copy (CL_id (id', ctyp'), V_id (a, ctyp'')), _) :: instrs
        when Name.compare id id' = 0 && ctyp_equal ctyp ctyp' && ctyp_equal ctyp' ctyp'' ->
          alias := Some a;
          scan ctyp id 1 instrs
      | 1, Some a, I_aux (I_copy (CL_id (a', ctyp'), V_id (id', ctyp'')), _) :: instrs
        when Name.compare a a' = 0 && Name.compare id id' = 0 && ctyp_equal ctyp ctyp' && ctyp_equal ctyp' ctyp'' ->
          scan ctyp id 2 instrs
      | 1, Some a, instr :: instrs ->
          if NameSet.mem a (instr_ids ~direct:true instr) then None else scan ctyp id 1 instrs
      | 2, Some _, I_aux (I_clear (ctyp', id'), _) :: instrs when Name.compare id id' = 0 && ctyp_equal ctyp ctyp' ->
          scan ctyp id 2 instrs
      | 2, Some _, instr :: instrs ->
          if NameSet.mem id (instr_ids ~direct:true instr) then None else scan ctyp id 2 instrs
      | 2, Some _, [] -> !alias
      | n, _, _ :: instrs when n = 0 || n > 2 -> scan ctyp id n instrs
      | _, _, I_aux (_, (_, l)) :: _ -> Reporting.unreachable l __POS__ "optimize_alias"
      | _, _, [] -> None
    in
    scan ctyp id 0
  in
  let remove_alias id alias = function
    | I_aux (I_copy (CL_id (id', _), V_id (alias', _)), _) when Name.compare id id' = 0 && Name.compare alias alias' = 0
      ->
        removed
    | I_aux (I_copy (CL_id (alias', _), V_id (id', _)), _) when Name.compare id id' = 0 && Name.compare alias alias' = 0
      ->
        removed
    | I_aux (I_clear (_, _), _) -> removed
    | instr -> instr
  in
  let rec opt = function
    | (I_aux (I_decl (ctyp, id), _) as instr) :: instrs as original_instrs -> (
        match pattern ctyp id instrs with
        | None ->
            let instrs' = opt instrs in
            if instrs == instrs' then original_instrs else instr :: instrs'
        | Some alias ->
            let instrs = List.map (map_instr (remove_alias id alias)) instrs in
            filter_instrs is_not_removed (List.map (instr_rename id alias) instrs)
      )
    | I_aux (I_block block, aux) :: instrs -> I_aux (I_block (opt block), aux) :: opt instrs
    | I_aux (I_try_block block, aux) :: instrs -> I_aux (I_try_block (opt block), aux) :: opt instrs
    | I_aux (I_if (cval, then_instrs, else_instrs), aux) :: instrs ->
        I_aux (I_if (cval, opt then_instrs, opt else_instrs), aux) :: opt instrs
    | instr :: instrs -> instr :: opt instrs
    | [] -> []
  in
  function
  | CDEF_aux (CDEF_fundef (function_id, heap_return, args, body), def_annot) ->
      [CDEF_aux (CDEF_fundef (function_id, heap_return, args, opt body), def_annot)]
  | cdef -> [cdef]

(** This optimization looks for patterns of the form

    {v
       create x : t;
       ... // some instructions
       { { { ... // and nested in any number of blocks
       create y : t;
       // modifications to y, no references to x
       x = y;
       // no changes to y
       kill y;
    v}

    If found we can replace y by x *)
module Combine_variables = struct
  type block_offset = int * int list

  let no_offset = (0, [])

  let deeper (n, blks) = (0, n :: blks)

  let next (n, blks) = (n + 1, blks)

  let reverse (x, xs) =
    let ys = List.rev (x :: xs) in
    (List.hd ys, List.tl ys)

  type state = Find of block_offset | Modify of block_offset * name | Kill of block_offset * name

  let pattern ctyp x =
    let rec scan state instrs =
      match state with
      | Find offset -> (
          match instrs with
          | I_aux (I_block block, _) :: instrs -> (
              match scan (Find (deeper offset)) block with None -> scan (Find (next offset)) instrs | result -> result
            )
          | I_aux (I_decl (ctyp', y), _) :: instrs when ctyp_equal ctyp ctyp' -> scan (Modify (offset, y)) instrs
          | _ :: instrs -> scan (Find offset) instrs
          | [] -> None
        )
      | Modify (offset, y) -> (
          match instrs with
          | I_aux (I_copy (CL_id (x', ctyp'), V_id (y', ctyp'')), _) :: instrs
            when Name.compare y y' = 0 && Name.compare x x' = 0 && ctyp_equal ctyp ctyp' && ctyp_equal ctyp' ctyp'' ->
              scan (Kill (offset, y)) instrs
          (* Ignore seemingly early clears of x, as this can happen along exception paths *)
          | I_aux (I_clear (_, x'), _) :: instrs when Name.compare x x' = 0 -> scan (Modify (offset, y)) instrs
          | instr :: instrs ->
              if instr_references ~read:x ~write:x ~direct:false instr then None else scan (Modify (offset, y)) instrs
          | [] -> None
        )
      | Kill (offset, y) -> (
          match instrs with
          | [] -> Some (offset, y)
          | I_aux (I_clear (ctyp', y'), _) :: _ when Name.compare y y' = 0 && ctyp_equal ctyp ctyp' -> Some (offset, y)
          | instr :: instrs ->
              if instr_references ~read:y ~write:y ~direct:false instr then None else scan (Kill (offset, y)) instrs
        )
    in
    scan (Find (0, []))

  let modify_error l = Reporting.unreachable l __POS__ "Combine variables optimisation failed"

  let modify l (skipped, nesting) ctyp x pattern_y =
    let rec traverse state instrs =
      match state with
      | Find (skipped, (child :: grandchildren as nesting)) -> (
          match instrs with
          | I_aux (I_block block, aux) :: instrs when skipped > 0 ->
              I_aux (I_block block, aux) :: traverse (Find (skipped - 1, nesting)) instrs
          | I_aux (I_block block, aux) :: instrs ->
              let block = traverse (Find (child, grandchildren)) block in
              I_aux (I_block block, aux) :: instrs
          | instr :: instrs -> instr :: traverse (Find (skipped, nesting)) instrs
          | [] -> modify_error l
        )
      | Find (skipped, []) -> (
          match instrs with
          | I_aux (I_decl (ctyp', y), _) :: instrs when ctyp_equal ctyp ctyp' ->
              assert (Name.compare pattern_y y = 0);
              traverse (Modify (no_offset, y)) instrs
          | I_aux (I_block block, aux) :: instrs when skipped > 0 ->
              I_aux (I_block block, aux) :: traverse (Find (skipped - 1, [])) instrs
          | instr :: instrs -> instr :: traverse (Find (skipped, [])) instrs
          | [] -> modify_error l
        )
      | Modify (_, y) -> (
          match instrs with
          | I_aux (I_copy (CL_id (x', ctyp'), V_id (y', ctyp'')), _) :: instrs
            when Name.compare y y' = 0 && Name.compare x x' = 0 && ctyp_equal ctyp ctyp' && ctyp_equal ctyp' ctyp'' ->
              traverse (Kill (no_offset, y)) instrs
          | instr :: instrs -> instr_rename y x instr :: traverse (Modify (no_offset, y)) instrs
          | [] -> modify_error l
        )
      | Kill (_, y) -> (
          match instrs with
          | I_aux (I_clear (ctyp', y'), _) :: instrs when Name.compare y y' = 0 && ctyp_equal ctyp ctyp' -> instrs
          | instr :: instrs -> instr :: traverse (Kill (no_offset, y)) instrs
          | [] -> []
        )
    in
    traverse (Find (skipped, nesting))

  let rec repeat_pattern l ctyp x instr instrs =
    match pattern ctyp x instrs with
    | None -> instrs
    | Some (offset, y) ->
        let instrs = modify l (reverse offset) ctyp x y instrs in
        repeat_pattern l ctyp x instr instrs

  class visitor ctyp_pred : jib_visitor =
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren
      method! vclexp _ = SkipChildren
      method! vcval _ = SkipChildren

      method! vinstrs =
        function
        | (I_aux (I_decl (ctyp, x), (_, l)) as instr) :: instrs when ctyp_pred ctyp -> (
            match pattern ctyp x instrs with
            | None -> DoChildren
            | Some (offset, y) ->
                let instrs = modify l (reverse offset) ctyp x y instrs in
                let instrs = repeat_pattern l ctyp x instr instrs in
                change_do_children (instr :: instrs)
          )
        | _ -> DoChildren

      method! vcdef = function CDEF_aux (CDEF_fundef _, _) -> DoChildren | _ -> SkipChildren
    end
end

let combine_variables ctx cdefs =
  visit_cdefs (new Combine_variables.visitor (fun ctyp -> not (is_stack_ctyp ctx ctyp))) cdefs

module Remove_stack_clears = struct
  let is_stack_clear ctx = function I_aux (I_clear (ctyp, _), _) -> is_stack_ctyp ctx ctyp | _ -> false

  class visitor ctx : jib_visitor =
    object
      inherit empty_jib_visitor

      method! vinstrs instrs =
        if List.exists (is_stack_clear ctx) instrs then
          change_do_children (List.filter (fun i -> not (is_stack_clear ctx i)) instrs)
        else DoChildren
    end
end

let remove_stack_clears ctx = visit_cdefs (new Remove_stack_clears.visitor ctx)

(* [to_bytes_le(n, get_slice_int(8 * n, value, 0))] is the source-level
   statement that only the low [n] bytes are observable.  Once [to_bytes_le]
   has been specialized to a fixed-byte result, its native helper already
   reads exactly those bytes.  Avoid first canonicalizing the intermediate
   bitvector with a u256 mask; standalone slices retain that mask. *)
let drop_redundant_to_bytes_mask =
  let low_bits_are_ones width bits =
    let rec check remaining = function
      | _ when remaining = 0 -> true
      | Sail2_values.B1 :: bits -> check (remaining - 1) bits
      | Sail2_values.B0 :: _ | Sail2_values.BU :: _ | [] -> false
    in
    List.length bits >= width && check width (List.rev bits)
  in
  let all_ones width = function
    | V_lit (VL_bits bits, ctyp) -> is_c_repr_u256 ctyp && low_bits_are_ones width bits
    | _ -> false
  in
  let to_bytes_width creturn callee width_arg =
    match (c_repr_fixed_bytes_length (creturn_ctyp creturn), width_arg) with
    | Some bytes, V_lit (VL_int width, _)
      when bytes <= 32
           && Big_int.equal width (Big_int.of_int bytes)
           && Util.starts_with ~prefix:"to_bytes_le" (string_of_id callee) ->
        Some bytes
    | _ -> None
  in
  let mask_covers_native_source mask source =
    let mask_width =
      match mask with
      | V_lit (VL_bits bits, ctyp) when is_c_repr_u256 ctyp && low_bits_are_ones 64 bits ->
          let rec count = function Sail2_values.B1 :: bits -> 1 + count bits | _ -> 0 in
          Some (count (List.rev bits))
      | _ -> None
    in
    match (mask_width, cval_ctyp source) with
    | Some width, ctyp when is_c_repr_u128 ctyp -> width >= 128
    | Some width, CT_fuint source_width -> width >= source_width
    | _ -> false
  in
  let rec rewrite = function
    | (I_aux (I_copy (CL_id (copy_id, copy_ctyp), V_call (Bvand, [source; mask])), _) as copy_instr)
      :: ( I_aux (I_funcall (creturn, extern, (callee, ctyp_args), [width_arg; V_id (arg_id, arg_ctyp)]), aux) as
           call_instr
         )
      :: instrs
      when Name.compare copy_id arg_id = 0
           && is_c_repr_u256 copy_ctyp && ctyp_equal copy_ctyp arg_ctyp
           && is_c_repr_u256 (cval_ctyp source) -> (
        match to_bytes_width creturn callee width_arg with
        | Some bytes when all_ones (8 * bytes) mask ->
            I_aux (I_funcall (creturn, extern, (callee, ctyp_args), [width_arg; source]), aux) :: rewrite instrs
        | _ -> copy_instr :: call_instr :: rewrite instrs
      )
    | (I_aux (I_decl (decl_ctyp, decl_id), _) as decl_instr)
      :: (I_aux (I_copy (CL_id (copy_id, copy_ctyp), V_call (Bvand, [source; mask])), _) as copy_instr)
      :: ( I_aux (I_funcall (creturn, extern, (callee, ctyp_args), [width_arg; V_id (arg_id, arg_ctyp)]), aux) as
           call_instr
         )
      :: instrs
      when Name.compare decl_id copy_id = 0
           && Name.compare copy_id arg_id = 0
           && is_c_repr_u256 decl_ctyp && ctyp_equal decl_ctyp copy_ctyp && ctyp_equal copy_ctyp arg_ctyp
           && is_c_repr_u256 (cval_ctyp source) -> (
        match to_bytes_width creturn callee width_arg with
        | Some bytes when all_ones (8 * bytes) mask ->
            I_aux (I_funcall (creturn, extern, (callee, ctyp_args), [width_arg; source]), aux) :: rewrite instrs
        | _ -> decl_instr :: rewrite (copy_instr :: call_instr :: instrs)
      )
    | I_aux (I_block block, aux) :: instrs -> I_aux (I_block (rewrite block), aux) :: rewrite instrs
    | I_aux (I_try_block block, aux) :: instrs -> I_aux (I_try_block (rewrite block), aux) :: rewrite instrs
    | I_aux (I_if (condition, then_instrs, else_instrs), aux) :: instrs ->
        I_aux (I_if (condition, rewrite then_instrs, rewrite else_instrs), aux) :: rewrite instrs
    | I_aux (I_copy (clexp, V_call (Bvand, [source; mask])), aux) :: instrs when mask_covers_native_source mask source
      ->
        I_aux (I_copy (clexp, source), aux) :: rewrite instrs
    | (I_aux (I_decl (ctyp, id), _) as instr) :: instrs when is_c_repr_u256 ctyp || is_c_repr_u320 ctyp ->
        let instrs = rewrite instrs in
        if List.exists (fun next -> NameSet.mem id (instr_ids ~direct:false next)) instrs then instr :: instrs
        else instrs
    | instr :: instrs -> instr :: rewrite instrs
    | [] -> []
  in
  List.map (function
    | CDEF_aux (CDEF_fundef (id, return, args, body), annot) ->
        CDEF_aux (CDEF_fundef (id, return, args, rewrite body), annot)
    | cdef -> cdef
    )

(* Fixed-bitvector primitives are materialized by ANF lowering before this
   point, so recognize compatible operations by following their JIB def/use
   webs.  Record the proved semantic operation explicitly before backend
   cleanup, rather than reconstructing it from the final C spelling. *)
let fuse_fixed_bitvector_webs cdefs =
  let fusions = ref 0 in
  let rec rewrite inherited_literals instrs =
    (* JIB introduces nested blocks around ANF fragments, while immutable Sail
       bindings can be defined in an enclosing block.  Carry literal facts
       forward through the lexical instruction stream, invalidating them at
       the first intervening write, so nested webs can use the same semantic
       constant without treating arbitrary C expressions as constants. *)
    let _, instrs =
      List.fold_left
        (fun (literal_environment, rewritten) instr ->
          let instr =
            match instr with
            | I_aux (I_block body, aux) -> I_aux (I_block (rewrite literal_environment body), aux)
            | I_aux (I_try_block body, aux) -> I_aux (I_try_block (rewrite literal_environment body), aux)
            | I_aux (I_if (condition, then_body, else_body), aux) ->
                I_aux
                  ( I_if
                      ( condition,
                        rewrite literal_environment then_body,
                        rewrite literal_environment else_body
                      ),
                    aux
                  )
            | instr -> instr
          in
          let literal_environment =
            match instr with
            | I_aux (I_copy (CL_id (name, _), (V_lit _ as literal)), _) ->
                NameMap.add name literal literal_environment
            | _ ->
                NameSet.fold
                  (fun name environment -> NameMap.remove name environment)
                  (instr_writes ~direct:false instr) literal_environment
          in
          (literal_environment, instr :: rewritten)
        )
        (inherited_literals, []) instrs
    in
    let instrs = List.rev instrs in
    let instructions = Array.of_list instrs in
    let count = Array.length instructions in
    let literal_value = function
      | V_lit (VL_int value, _) -> Some value
      | V_lit (VL_bits bits, _) ->
          List.fold_left
            (fun value bit ->
              Option.bind value (fun value ->
                  match bit with
                  | Sail2_values.B0 -> Some (Big_int.mul value (Big_int.of_int 2))
                  | Sail2_values.B1 -> Some (Big_int.succ (Big_int.mul value (Big_int.of_int 2)))
                  | Sail2_values.BU -> None
              )
            )
            (Some Big_int.zero) bits
      | _ -> None
    in
    let literal_index value =
      match literal_value value with
      | Some value
        when Big_int.less_equal Big_int.zero value
             && Big_int.less_equal value (Big_int.of_int Stdlib.max_int) ->
          Some (Big_int.to_int value)
      | Some _ | None -> None
    in
    let slice_definitions =
      Array.fold_left
        (fun (index, definitions) (I_aux (instr, _)) ->
          let definitions =
            match instr with
            | I_copy (CL_id (name, _), V_call ((Slice width | Proven_slice (width, _)), [source; start])) -> (
                match literal_index start with
                | Some start -> NameMap.add name (index, width, source, start) definitions
                | None -> definitions
              )
            | _ -> definitions
          in
          (index + 1, definitions)
        )
        (0, NameMap.empty) instructions
      |> snd
    in
    let literal_definitions =
      Array.fold_left
        (fun (index, definitions) (I_aux (instr, _)) ->
          let definitions =
            match instr with
            | I_copy (CL_id (name, _), (V_lit _ as literal)) ->
                NameMap.add name (index, literal) definitions
            | _ -> definitions
          in
          (index + 1, definitions)
        )
        (0, NameMap.empty) instructions
      |> snd
    in
    let logical_right_shift_definitions =
      Array.fold_left
        (fun (index, definitions) (I_aux (instr, _)) ->
          let definitions =
            match instr with
            | I_copy
                ( CL_id (name, _),
                  V_call (((Bvshiftr | Proven_bvshiftr _) as op), [source; amount])
                ) ->
                NameMap.add name (index, op, source, amount) definitions
            | _ -> definitions
          in
          (index + 1, definitions)
        )
        (0, NameMap.empty) instructions
      |> snd
    in
    let owns_lifecycle name = function
      | I_aux
          ((I_decl (_, candidate) | I_reset (_, candidate) | I_clear (_, candidate) | I_init (_, candidate, _)), _)
        ->
          Name.compare name candidate = 0
      | _ -> false
    in
    let private_temporary name definition_index use_index =
      let rec loop index =
        if index = count then true
        else
          let instr = instructions.(index) in
          let allowed =
            index = definition_index || index = use_index || owns_lifecycle name instr
            || not (NameSet.mem name (instr_ids ~direct:false instr))
          in
          allowed && loop (index + 1)
      in
      loop 0
    in
    let source_is_stable source first last =
      match source with
      | V_id (source_name, _) ->
          let rec loop index =
            index >= last
            ||
            (not (NameSet.mem source_name (instr_writes ~direct:false instructions.(index)))
            && loop (index + 1)
            )
          in
          loop (first + 1)
      | V_lit _ -> true
      | _ -> false
    in
    let same_source left right =
      match (left, right) with
      | V_id (left_name, left_ctyp), V_id (right_name, right_ctyp) ->
          Name.compare left_name right_name = 0 && ctyp_equal left_ctyp right_ctyp
      | V_lit (left_lit, left_ctyp), V_lit (right_lit, right_ctyp) ->
          Stdlib.compare left_lit right_lit = 0 && ctyp_equal left_ctyp right_ctyp
      | _ -> false
    in
    let resolve_literal use_index = function
      | V_lit _ as literal -> Option.map (fun value -> (None, value)) (literal_value literal)
      | V_id (name, ctyp) as value -> (
          match NameMap.find_opt name literal_definitions with
          | Some (definition_index, literal)
            when definition_index < use_index
                 && ctyp_equal ctyp (cval_ctyp literal)
                 && source_is_stable value definition_index use_index ->
              Option.map (fun literal -> (Some (name, definition_index), literal)) (literal_value literal)
          | Some _ -> None
          | None -> (
              match NameMap.find_opt name inherited_literals with
              | Some literal
                when ctyp_equal ctyp (cval_ctyp literal) && source_is_stable value (-1) use_index ->
                  Option.map (fun literal -> (None, literal)) (literal_value literal)
              | Some _ | None -> None
            )
        )
      | _ -> None
    in
    let resolve_proven_logical_right_shift use_index = function
      | V_id (name, ctyp) -> (
          match NameMap.find_opt name logical_right_shift_definitions with
          | Some (definition_index, op, source, amount)
            when definition_index < use_index
                 && private_temporary name definition_index use_index
                 && ctyp_equal ctyp (cval_ctyp source)
                 && source_is_stable source definition_index use_index -> (
              let proven =
                match op with
                | Proven_bvshiftr 64 -> true
                | Bvshiftr -> (
                    match literal_value amount with
                    | Some amount ->
                        let interval = Some (amount, amount) in
                        Option.is_some
                          (Jib_semantics.prove_shift_count_interval ~index:1 ~interval ~carrier_width:64)
                    | None -> false
                  )
                | Proven_bvshiftr _ | _ -> false
              in
              if proven then Some (name, definition_index, source, amount) else None
            )
          | Some _ | None -> None
        )
      | _ -> None
    in
    let replacements = Hashtbl.create 2 in
    let removed = ref NameSet.empty in
    Array.iteri
      (fun concat_index (I_aux (instr, aux)) ->
        match instr with
        | I_copy (destination, V_call (Concat, [V_id (left_name, _); V_id (right_name, _)])) -> (
            match (NameMap.find_opt left_name slice_definitions, NameMap.find_opt right_name slice_definitions) with
            | ( Some (left_index, left_width, left_source, left_start),
                Some (right_index, right_width, right_source, right_start) ) ->
                let result_width = left_width + right_width in
                let source_width = match cval_ctyp left_source with CT_fbits width -> Some width | _ -> None in
                let semantic_rotation =
                  left_start = 0 && right_start = left_width && 0 < left_width && 0 < right_width
                in
                let definitions_precede_use = left_index < concat_index && right_index < concat_index in
                let web_is_private =
                  private_temporary left_name left_index concat_index
                  && private_temporary right_name right_index concat_index
                in
                let sources_match = same_source left_source right_source in
                let source_is_wide_enough =
                  match source_width with Some width -> result_width <= width && result_width <= 64 | None -> false
                in
                let stable_source = source_is_stable left_source (min left_index right_index) concat_index in
                if
                  semantic_rotation && definitions_precede_use && web_is_private && sources_match
                  && source_is_wide_enough && stable_source
                  && ctyp_equal (clexp_ctyp destination) (CT_fbits result_width)
                then (
                  Hashtbl.add replacements concat_index
                    (I_aux (I_copy (destination, V_call (Bvrotr (result_width, left_width), [left_source])), aux));
                  removed := NameSet.add left_name (NameSet.add right_name !removed);
                  incr fusions
                )
            | _ -> ()
          )
        | _ -> ()
      )
      instructions;
    Array.iteri
      (fun mask_index (I_aux (instr, aux)) ->
        match instr with
        | I_copy (destination, V_call (Bvand, [left; right])) -> (
            let web =
              List.find_map
                (fun (shifted, mask) ->
                  let shift = resolve_proven_logical_right_shift mask_index shifted in
                  let literal = resolve_literal mask_index mask in
                  Option.bind shift (fun shift ->
                      Option.map (fun literal -> (shift, mask, literal)) literal
                  )
                )
                [(left, right); (right, left)]
            in
            match web with
            | ( Some
                  ( (shift_name, shift_index, source, amount),
                    mask,
                    (mask_definition, mask_value)
                  ) ) -> (
                match (cval_ctyp source, clexp_ctyp destination) with
                | CT_fbits source_width, CT_fbits result_width
                  when 0 < source_width && source_width <= 64 && source_width = result_width
                       && ctyp_equal (cval_ctyp mask) (CT_fbits result_width) -> (
                    match Jib_semantics.prove_low_mask_width ~carrier_width:result_width ~mask:mask_value with
                    | Some slice_width when slice_width <= source_width ->
                        let slice = V_call (Proven_slice (slice_width, 64), [source; amount]) in
                        let extracted =
                          if slice_width = result_width then slice
                          else V_call (Zero_extend result_width, [slice])
                        in
                        Hashtbl.replace replacements mask_index
                          (I_aux (I_copy (destination, extracted), aux));
                        removed := NameSet.add shift_name !removed;
                        ( match mask_definition with
                        | Some (mask_name, definition_index)
                          when private_temporary mask_name definition_index mask_index ->
                            removed := NameSet.add mask_name !removed
                        | Some _ | None -> ()
                        );
                        incr fusions
                    | Some _ | None -> ()
                  )
                | _ -> ()
              )
            | None -> ()
          )
        | _ -> ()
      )
      instructions;
    Array.to_list instructions
    |> List.mapi (fun index instr ->
           match Hashtbl.find_opt replacements index with
           | Some replacement -> Some replacement
           | None -> (
               match instr with
               | I_aux
                   ( ( I_decl (_, name) | I_reset (_, name) | I_clear (_, name)
                     | I_init (_, name, _) ),
                     _
                   )
                 when NameSet.mem name !removed ->
                   None
               | I_aux (I_copy (CL_id (name, _), _), _) when NameSet.mem name !removed -> None
               | _ -> Some instr
             )
       )
    |> List.filter_map Fun.id
  in
  let cdefs =
    List.map
      (function
        | CDEF_aux (CDEF_fundef (id, return, args, body), annot) ->
            CDEF_aux (CDEF_fundef (id, return, args, rewrite NameMap.empty body), annot)
        | cdef -> cdef
      )
      cdefs
  in
  (cdefs, !fusions)

let optimize ~have_rts ~specialize_c ctx recursive_functions cdefs =
  let nothing cdefs = cdefs in
  cdefs
  |> (if !optimize_alias then List.concat_map remove_alias else nothing)
  |> (if !optimize_alias then combine_variables ctx else nothing)
  (* We need the runtime to initialize hoisted allocations *)
  |> ( if !optimize_hoist_allocations && have_rts then List.concat_map (hoist_allocations recursive_functions)
       else nothing
     )
  |> (if specialize_c then drop_redundant_to_bytes_mask else nothing)
  |> remove_stack_clears ctx

(**************************************************************************)
(* 6. Code generation                                                     *)
(**************************************************************************)

let mk_regexp_check regexp_str =
  let regexp = Str.regexp regexp_str in
  fun s -> Str.string_match regexp s 0

let valid_c_identifier = mk_regexp_check "^[A-Za-z_][A-Za-z0-9_]*$"

let c_int_type_name = mk_regexp_check "^[u]?int[0-9]+_t$"

(* The code generator produces a list of C/C++ definitions and declarations
   which go in different places depending on their type and whether we
   are generating C or C++ code.
*)
type file_doc =
  (* Declaration of a custom type (typedef int foo;). This goes in a namespace in C++. *)
  | TypeDeclaration of document
  (* Model function declaration. This goes in a struct in C++ to become a struct method. *)
  | FunctionDeclaration of document
  (* Function definitions. These always go in the .c/.cpp file. *)
  | FunctionDefinition of document
  (* Variable declaration (extern int foo;) and definition (int foo = 4;).
     In C++ we only take the definition and put it in the struct.
     In C the declaration goes in the header and the definition goes in the impl. *)
  | VariableDeclaration of document
  | VariableDefinition of document
  (* Pure static utility functions created for the model's types, e.g. to initialise
     enums, access vector elements, etc. These don't have corresponding declarations. *)
  | StaticFunctionDefinition of document

module type CODEGEN_CONFIG = sig
  val includes : string list
  val header_includes : string list
  val no_main : bool
  val no_lib : bool
  val no_rts : bool
  val no_mangle : bool
  val reserved_words : Util.StringSet.t
  val overrides : string Name_generator.Overrides.t
  val branch_coverage : out_channel option
  val assert_to_exception : bool
  val preserve_types : IdSet.t
  val c_repr_unsigned : int Bindings.t
  val c_repr_signed : int Bindings.t
  val c_repr_u256 : IdSet.t
  val c_repr_fixed_bytes : int Bindings.t
  val specialize_c : bool
  val require_bounded_int : bool
  val optimized_model : bool
  val package_name : string
  val cpp : bool
  val cpp_class_name : string
  val cpp_namespace : string
  val cpp_derive_from : string option
end

module Codegen (Config : CODEGEN_CONFIG) = struct
  open Printf

  type c_module = {
    name : string;
    file_stem : string;
    files : string list;
    requires : string list;
  }

  type c_module_output = {
    name : string;
    file_stem : string;
    header : string;
    implementation : string;
  }

  let requested_modules : (string * c_module list) option ref = ref None
  let generated_modules : c_module_output list option ref = ref None
  let emitted_external_functions = ref Util.StringSet.empty

  let has_prefix prefix s =
    if String.length s < String.length prefix then false else String.sub s 0 (String.length prefix) = prefix

  let has_bad_prefix s =
    has_prefix "sail_" s || has_prefix "Sail_" s || has_prefix "SAIL_" s || has_prefix "undefined_" s

  (* Prefix to function name in definitions. *)
  let class_impl_prefix () = if Config.cpp then Config.cpp_class_name ^ "::" else ""

  let valid_readable_name s =
    valid_c_identifier s
    && (not (Util.StringSet.mem s Keywords.c_reserved_words))
    && (not (Util.StringSet.mem s Keywords.c_used_words))
    && (not (Util.StringSet.mem s Config.reserved_words))
    && (not (has_bad_prefix s))
    && not (c_int_type_name s)

  let sanitize_readable_name s =
    let is_alpha c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') in
    let is_digit c = '0' <= c && c <= '9' in
    let buffer = Buffer.create (String.length s) in
    String.iteri
      (fun i c ->
        if is_alpha c || c = '_' || (i > 0 && is_digit c) then Buffer.add_char buffer c else Buffer.add_char buffer '_'
      )
      s;
    let name = Buffer.contents buffer in
    let name = if name = "" then "tmp" else name in
    if valid_readable_name name then name
    else (
      let name = "tmp_" ^ name in
      if valid_readable_name name then name else "tmp"
    )

  (* Jib monomorphization appends the concrete type arguments as
     [name<arg,...>].  Those brackets cannot appear in C identifiers, but the
     type structure is still useful provenance.  Under [--c-no-mangle], keep
     it readable rather than immediately falling back to the opaque zencoding. *)
  let readable_specialized_name s =
    let buffer = Buffer.create (String.length s + 8) in
    String.iter
      (function
        | '<' -> Buffer.add_string buffer "_of_"
        | ',' -> Buffer.add_string buffer "_and_"
        | '>' -> ()
        | c -> Buffer.add_char buffer c
        )
      s;
    sanitize_readable_name (Buffer.contents buffer)

  (* = {} is required to zero-initialise the types. In C output mode this is unnecessary because
    they are emitted as globals and are therefore automatically zero-initialised. However in C++ mode they
    become struct members and aren't initialised. The `sail_set_abstract_()` function assumes that they
    have been initialised.

    Note, `int foo = {};` is legal in C23, so we can use it unconditionally eventually. *)
  let variable_zero_init () = if Config.cpp then " = {}" else ""

  module NameGen =
    Name_generator.Make
      (struct
        type style = unit

        let allowed s =
          let valid_name s =
            valid_c_identifier s
            && (not (Util.StringSet.mem s Keywords.c_reserved_words))
            && (not (Util.StringSet.mem s Keywords.c_used_words))
            && (not (Util.StringSet.mem s Config.reserved_words))
            && (not (has_bad_prefix s))
            && not (c_int_type_name s)
          in
          (not Config.no_mangle) || valid_name s

        let pretty () s = if Config.no_mangle then s else Util.zencode_string s

        let mangle () s =
          if Config.no_mangle && String.contains s '<' then readable_specialized_name s else Util.zencode_string s

        let variant s = function 0 -> s | n -> s ^ string_of_int n

        let overrides = Config.overrides
      end)
      ()

  let sgen_id id = NameGen.to_string () id

  let sgen_uid (id, ctyps) =
    match ctyps with
    | [] -> NameGen.to_string () id
    | _ -> NameGen.translate () (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

  let ssa_num n = if n = -1 then "" else "/" ^ string_of_int n

  let sgen_non_generated_name = function
    | Name (id, n) -> NameGen.to_string () id ^ ssa_num n
    | Abstract id -> NameGen.to_string ~prefix:"abstract_" () id
    | Have_exception n -> "have_exception" ^ ssa_num n
    | Return n -> "return" ^ ssa_num n
    | Current_exception n ->
        (if Config.optimized_model then "current_exception" else "(*current_exception)") ^ ssa_num n
    | Throw_location n -> "throw_location" ^ ssa_num n
    | Memory_writes n -> "memory_writes" ^ ssa_num n
    | Channel (chan, n) -> (
        match chan with Chan_stdout -> "stdout" ^ ssa_num n | Chan_stderr -> "stderr" ^ ssa_num n
      )
    | Gen _ -> assert false

  let local_generated_names = ref NameMap.empty
  let local_used_names = ref Util.StringSet.empty

  let rec allocate_local_name base suffix =
    let candidate = if suffix = 0 then base else base ^ "_" ^ string_of_int suffix in
    if Util.StringSet.mem candidate !local_used_names then allocate_local_name base (suffix + 1)
    else (
      local_used_names := Util.StringSet.add candidate !local_used_names;
      candidate
    )

  let readable_generated_name name source_name =
    match NameMap.find_opt name !local_generated_names with
    | Some generated_name -> generated_name
    | None ->
        let base = sanitize_readable_name (Option.value ~default:"tmp" source_name) in
        let generated_name = allocate_local_name base 0 in
        local_generated_names := NameMap.add name generated_name !local_generated_names;
        generated_name

  let sgen_name = function
    | Gen (v1, v2, n, source_name, _) as name ->
        if Config.no_mangle then readable_generated_name name source_name
        else NameGen.to_string () (mk_id (sprintf "%d.%d" v1 v2)) ^ ssa_num n
    | name -> sgen_non_generated_name name

  let prepare_local_name_scope def =
    local_generated_names := NameMap.empty;
    local_used_names := Util.StringSet.empty;
    if Config.no_mangle then (
      let reserve =
        object
          inherit empty_jib_visitor

          method! vname name =
            ( match name with
            | Gen _ -> ()
            | name -> local_used_names := Util.StringSet.add (sgen_non_generated_name name) !local_used_names
            );
            None
        end
      in
      ignore (visit_cdef reserve def)
    )

  let codegen_id id = string (sgen_id id)

  let sgen_function_id id =
    let str = NameGen.to_string () id in
    if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)

  let sgen_function_uid uid =
    let str = sgen_uid uid in
    if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)

  let codegen_function_id id = string (sgen_function_id id)

  let readable_ctyp_names = ref CTMap.empty
  let readable_ctyp_names_used = ref Util.StringSet.empty

  let rec readable_ctyp_stem = function
    | ctyp when is_c_repr_u320 ctyp -> "u320"
    | ctyp when is_c_repr_u256 ctyp -> "u256"
    | ctyp when is_c_repr_fixed_bytes ctyp ->
        "fixed_bytes_" ^ string_of_int (Option.get (c_repr_fixed_bytes_length ctyp))
    | CT_unit -> "unit"
    | CT_bool -> "bool"
    | CT_fbits n -> "bits_" ^ string_of_int n
    | CT_sbits n -> "small_bits_" ^ string_of_int n
    | CT_fint n -> "int_" ^ string_of_int n
    | CT_fuint n -> "uint_" ^ string_of_int n
    | CT_constant n -> "constant_" ^ sanitize_readable_name (Big_int.to_string n)
    | CT_lint -> "int"
    | CT_lbits -> "bits"
    | CT_tup ctyps -> "tuple_" ^ String.concat "_" (List.map readable_ctyp_stem ctyps)
    | CT_struct (id, []) | CT_variant (id, []) -> sgen_id id
    | CT_struct (id, ctyps) | CT_variant (id, ctyps) ->
        sgen_id id ^ "_of_" ^ String.concat "_" (List.map readable_ctyp_stem ctyps)
    | CT_enum id -> sgen_id id
    | CT_list ctyp -> "list_" ^ readable_ctyp_stem ctyp
    | CT_vector ctyp -> "vector_" ^ readable_ctyp_stem ctyp
    | CT_fvector (length, ctyp) -> "vector_" ^ string_of_int length ^ "_" ^ readable_ctyp_stem ctyp
    | CT_string -> "string"
    | CT_real -> "real"
    | CT_json -> "json"
    | CT_json_key -> "json_key"
    | CT_ref ctyp -> "ref_" ^ readable_ctyp_stem ctyp
    | CT_float n -> "float_" ^ string_of_int n
    | CT_rounding_mode -> "rounding_mode"
    | CT_memory_writes -> "memory_writes"
    | CT_poly kid -> "poly_" ^ sanitize_readable_name (string_of_kid kid)

  let rec allocate_readable_ctyp_name ctyp base suffix =
    let candidate = if suffix = 0 then base else base ^ "_" ^ string_of_int suffix in
    if Util.StringSet.mem candidate !readable_ctyp_names_used then allocate_readable_ctyp_name ctyp base (suffix + 1)
    else (
      readable_ctyp_names := CTMap.add ctyp candidate !readable_ctyp_names;
      readable_ctyp_names_used := Util.StringSet.add candidate !readable_ctyp_names_used;
      candidate
    )

  let readable_ctyp_name ctyp =
    match CTMap.find_opt ctyp !readable_ctyp_names with
    | Some name -> name
    | None -> allocate_readable_ctyp_name ctyp (sanitize_readable_name (readable_ctyp_stem ctyp)) 0

  let composite_ctyp_name legacy ctyp = if Config.no_mangle then readable_ctyp_name ctyp else Util.zencode_string legacy

  let native_c_integer_width width =
    if width <= 8 then 8 else if width <= 16 then 16 else if width <= 32 then 32 else 64

  let is_native_unsigned_integer = function CT_fuint width -> width <= 64 | _ -> false
  let is_native_signed_integer = function CT_fint width -> width <= 64 | _ -> false

  let rec sgen_ctyp = function
    | ctyp when is_c_repr_u128 ctyp -> "sail_u128"
    | ctyp when is_c_repr_u256 ctyp -> "sail_u256"
    | ctyp when is_c_repr_u320 ctyp -> "sail_u320"
    | ctyp when is_c_repr_fixed_bytes ctyp ->
        "sail_fixed_bytes_" ^ string_of_int (Option.get (c_repr_fixed_bytes_length ctyp))
    | CT_unit -> "unit"
    | CT_bool -> "bool"
    | CT_fbits _ -> "uint64_t"
    | CT_sbits _ -> "sbits"
    | CT_fint width -> if width <= 64 then "int" ^ string_of_int (native_c_integer_width width) ^ "_t" else "__int128"
    | CT_fuint width -> "uint" ^ string_of_int (native_c_integer_width width) ^ "_t"
    | CT_constant _ -> "int64_t"
    | CT_lint -> "sail_int"
    | CT_lbits -> "lbits"
    | CT_tup _ as tup -> "struct " ^ composite_ctyp_name ("tuple_" ^ string_of_ctyp tup) tup
    | CT_struct (id, _) -> "struct " ^ sgen_id id
    | CT_enum id -> "enum " ^ sgen_id id
    | CT_variant (id, _) -> "struct " ^ sgen_id id
    | CT_list _ as l -> composite_ctyp_name (string_of_ctyp l) l
    | CT_vector _ as v -> composite_ctyp_name (string_of_ctyp v) v
    | CT_fvector _ as v -> composite_ctyp_name (string_of_ctyp v) v
    | CT_string -> "sail_string"
    | CT_real -> "real"
    | CT_json -> "sail_config_json"
    | CT_json_key -> "sail_config_key"
    | CT_ref ctyp -> sgen_ctyp ctyp ^ "*"
    | CT_float n -> "float" ^ string_of_int n ^ "_t"
    | CT_rounding_mode -> "uint_fast8_t"
    | CT_memory_writes -> "sail_memory_writes"
    | CT_poly _ -> "POLY" (* c_error "Tried to generate code for non-monomorphic type" *)

  let rec sgen_ctyp_name = function
    | ctyp when is_c_repr_u128 ctyp -> "u128"
    | ctyp when is_c_repr_u256 ctyp -> "u256"
    | ctyp when is_c_repr_u320 ctyp -> "u320"
    | ctyp when is_c_repr_fixed_bytes ctyp ->
        "fixed_bytes_" ^ string_of_int (Option.get (c_repr_fixed_bytes_length ctyp))
    | CT_unit -> "unit"
    | CT_bool -> "bool"
    | CT_fbits _ -> "fbits"
    | CT_sbits _ -> "sbits"
    | CT_fint width -> if width <= 64 then "mach_int" else "int_" ^ string_of_int width
    | CT_fuint _ -> "mach_uint"
    | CT_constant _ -> "mach_int"
    | CT_lint -> "sail_int"
    | CT_lbits -> "lbits"
    | CT_tup _ as tup -> composite_ctyp_name ("tuple_" ^ string_of_ctyp tup) tup
    | CT_struct (id, _) -> sgen_id id
    | CT_enum id -> sgen_id id
    | CT_variant (id, _) -> sgen_id id
    | CT_list _ as l -> composite_ctyp_name (string_of_ctyp l) l
    | CT_vector _ as v -> composite_ctyp_name (string_of_ctyp v) v
    | CT_fvector _ as v -> composite_ctyp_name (string_of_ctyp v) v
    | CT_string -> "sail_string"
    | CT_real -> "real"
    | CT_json -> "sail_config_json"
    | CT_json_key -> "sail_config_key"
    | CT_ref ctyp -> "ref_" ^ sgen_ctyp_name ctyp
    | CT_float n -> "float" ^ string_of_int n
    | CT_rounding_mode -> "rounding_mode"
    | CT_memory_writes -> "sail_memory_writes"
    | CT_poly _ -> "POLY" (* c_error "Tried to generate code for non-monomorphic type" *)

  let sgen_const_ctyp = function CT_string -> "const_sail_string" | ty -> sgen_ctyp ty

  let sgen_mask n =
    if n = 0 then "UINT64_C(0)"
    else if n <= 64 then (
      let chars_F = String.make (n / 4) 'F' in
      let first = match n mod 4 with 0 -> "" | 1 -> "1" | 2 -> "3" | 3 -> "7" | _ -> assert false in
      "UINT64_C(0x" ^ first ^ chars_F ^ ")"
    )
    else failwith "Tried to create a mask literal for a vector greater than 64 bits."

  let sgen_u256_bits bs =
    let length = List.length bs in
    if length > 256 then c_error "Tried to create a u256 literal wider than 256 bits";
    let padded = Util.list_init (256 - length) (fun _ -> Sail2_values.B0) @ bs in
    let rec chunks size bits =
      match bits with
      | [] -> []
      | _ ->
          let rec take n acc rest =
            if n = 0 then (List.rev acc, rest)
            else (match rest with bit :: rest -> take (n - 1) (bit :: acc) rest | [] -> assert false)
          in
          let chunk, rest = take size [] bits in
          chunk :: chunks size rest
    in
    let limbs =
      chunks 64 padded |> List.rev |> List.map (fun limb -> "UINT64_C(" ^ Sail2_values.show_bitlist limb ^ ")")
    in
    "((sail_u256){{" ^ String.concat ", " limbs ^ "}})"

  let sgen_u128_int value =
    let mask = max_uint 64 in
    let lo = Big_int.bitwise_and value mask in
    let hi = Big_int.shift_right value 64 in
    "((sail_u128){{UINT64_C(" ^ Big_int.to_string lo ^ "), UINT64_C(" ^ Big_int.to_string hi ^ ")}})"

  let sgen_u256_int value =
    let mask = max_uint 64 in
    let limb shift = Big_int.shift_right value shift |> fun value -> Big_int.bitwise_and value mask in
    "((sail_u256){{UINT64_C("
    ^ Big_int.to_string (limb 0)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 64)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 128)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 192)
    ^ ")}})"

  let sgen_u320_int value =
    let mask = max_uint 64 in
    let limb shift = Big_int.shift_right value shift |> fun value -> Big_int.bitwise_and value mask in
    "((sail_u320){{UINT64_C("
    ^ Big_int.to_string (limb 0)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 64)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 128)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 192)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 256)
    ^ ")}})"

  let sgen_i128_int value =
    let unsigned_i128 value =
      let mask = max_uint 64 in
      let lo = Big_int.bitwise_and value mask in
      let hi = Big_int.shift_right value 64 in
      "((((unsigned __int128)UINT64_C(" ^ Big_int.to_string hi ^ ")) << 64) | UINT64_C(" ^ Big_int.to_string lo ^ "))"
    in
    if Big_int.less value Big_int.zero then (
      let magnitude_minus_one = Big_int.pred (Big_int.negate value) in
      "(-((__int128)" ^ unsigned_i128 magnitude_minus_one ^ ") - 1)"
    )
    else "((__int128)" ^ unsigned_i128 value ^ ")"

  let sgen_value ctyp = function
    | VL_bits bs when is_c_repr_u256 ctyp -> sgen_u256_bits bs
    | VL_bits [] -> "UINT64_C(0)"
    | VL_bits bs -> "UINT64_C(" ^ Sail2_values.show_bitlist bs ^ ")"
    | VL_int i -> (
        match ctyp with
        | ctyp when is_c_repr_u320 ctyp -> sgen_u320_int i
        | ctyp when is_c_repr_u256 ctyp -> sgen_u256_int i
        | ctyp when is_c_repr_u128 ctyp -> sgen_u128_int i
        | CT_fuint width when width < 64 -> "((" ^ sgen_ctyp ctyp ^ ")UINT64_C(" ^ Big_int.to_string i ^ "))"
        | CT_fuint _ -> "UINT64_C(" ^ Big_int.to_string i ^ ")"
        | CT_fint width when width > 64 -> sgen_i128_int i
        | CT_fint width when width < 64 -> "((" ^ sgen_ctyp ctyp ^ ")INT64_C(" ^ Big_int.to_string i ^ "))"
        | _ -> if Big_int.equal i (min_int 64) then "INT64_MIN" else "INT64_C(" ^ Big_int.to_string i ^ ")"
      )
    | VL_bool true -> "true"
    | VL_bool false -> "false"
    | VL_unit -> "UNIT"
    | VL_real str -> str
    | VL_string str -> "\"" ^ str ^ "\""
    | VL_enum element -> Util.zencode_string element
    | VL_ref r -> "&" ^ sgen_id (mk_id r)
    | VL_undefined -> Reporting.unreachable Parse_ast.Unknown __POS__ "Cannot generate C value for an undefined literal"

  let sgen_tuple_id n = sgen_id (mk_id ("tup" ^ string_of_int n))

  let rec sgen_cval = function
    | V_id (id, _) -> sgen_name id
    | V_member (id, _) -> sgen_id id
    | V_lit (vl, ctyp) -> sgen_value ctyp vl
    | V_call (op, cvals) -> sgen_call op cvals
    | V_field (f, field, _) -> sprintf "%s.%s" (sgen_cval f) (sgen_id field)
    | V_tuple_member (f, _, n) -> sprintf "%s.%s" (sgen_cval f) (sgen_tuple_id n)
    | V_ctor_kind (f, ctor) -> sgen_cval f ^ ".kind" ^ " != Kind_" ^ sgen_uid ctor
    | V_struct (fields, _) ->
        sprintf "{%s}" (Util.string_of_list ", " (fun (field, cval) -> sgen_id field ^ " = " ^ sgen_cval cval) fields)
    | V_ctor_unwrap (f, ctor, _) -> sprintf "%s.variants.%s" (sgen_cval f) (sgen_uid ctor)
    | V_tuple _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Cannot generate C value for a tuple literal"

  and sgen_proven_native_binop operator v1 v2 =
    let raw () = sprintf "(%s %s %s)" (sgen_cval v1) operator (sgen_cval v2) in
    match cval_ctyp v1 with
    | CT_fuint width when width < 32 ->
        sprintf "((%s)(((uint32_t)%s) %s ((uint32_t)%s)))" (sgen_ctyp (CT_fuint width)) (sgen_cval v1) operator
          (sgen_cval v2)
    | CT_fint width when width < 32 ->
        sprintf "((%s)(((int32_t)%s) %s ((int32_t)%s)))" (sgen_ctyp (CT_fint width)) (sgen_cval v1) operator
          (sgen_cval v2)
    | CT_fint _ | CT_fuint _ -> raw ()
    | ctyp when is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp ->
        (* A semantic proof can be attached while an integer still has a
           scalar JIB carrier and survive a later def/call-graph
           specialization to a plain wide-value carrier.  The proof remains
           valid, but C operators do not apply to those structs; use the same
           allocation-free helpers as ordinary wide arithmetic. *)
        let op =
          match operator with
          | "+" -> Iadd
          | "-" -> Isub
          | "*" -> Imul
          | "/" -> Idiv
          | "%" -> Imod
          | _ -> assert false
        in
        sgen_call op [v1; v2]
    | _ ->
        failwith
          (Printf.sprintf "Proven native arithmetic requires fixed integer operands, got %s and %s"
             (string_of_ctyp (cval_ctyp v1)) (string_of_ctyp (cval_ctyp v2)))

  and sgen_call op cvals =
    let u320_of value =
      match cval_ctyp value with
      | ctyp when is_c_repr_u320 ctyp -> sgen_cval value
      | ctyp when is_c_repr_u256 ctyp -> sprintf "u320_of_u256(%s)" (sgen_cval value)
      | ctyp when is_c_repr_u128 ctyp -> sprintf "u320_of_u128(%s)" (sgen_cval value)
      | CT_fuint _ -> sprintf "u320_of_u64(%s)" (sgen_cval value)
      | ctyp -> failwith ("Cannot widen " ^ string_of_ctyp ctyp ^ " to sail_u320")
    in
    match (op, cvals) with
    | Bnot, [v] -> "!(" ^ sgen_cval v ^ ")"
    | Band, vs -> "(" ^ Util.string_of_list " && " sgen_cval vs ^ ")"
    | Bor, vs -> "(" ^ Util.string_of_list " || " sgen_cval vs ^ ")"
    | List_hd, [v] -> sprintf "(%s).hd" ("*" ^ sgen_cval v)
    | List_tl, [v] -> sprintf "(%s).tl" ("*" ^ sgen_cval v)
    | List_is_empty, [v] -> sprintf "(%s == NULL)" (sgen_cval v)
    | Eq, [v1; v2] -> (
        match (cval_ctyp v1, cval_ctyp v2) with
        | CT_sbits _, _ -> sprintf "eq_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u320 left || is_c_repr_u320 right ->
            sprintf "eq_u320(%s, %s)" (u320_of v1) (u320_of v2)
        | left, right when is_c_repr_u256 left && is_c_repr_u128 right ->
            sprintf "u256_eq_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u128 left && is_c_repr_u256 right ->
            sprintf "u256_eq_u128(%s, %s)" (sgen_cval v2) (sgen_cval v1)
        | left, CT_fuint _ when is_c_repr_u128 left -> sprintf "u128_eq_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, right when is_c_repr_u128 right -> sprintf "u128_eq_u64(%s, %s)" (sgen_cval v2) (sgen_cval v1)
        | left, CT_fuint _ when is_c_repr_u256 left -> sprintf "u256_eq_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, right when is_c_repr_u256 right -> sprintf "u256_eq_u64(%s, %s)" (sgen_cval v2) (sgen_cval v1)
        | ctyp, _ when is_c_repr_value ctyp ->
            sprintf "eq_%s(%s, %s)" (sgen_ctyp_name ctyp) (sgen_cval v1) (sgen_cval v2)
        | _ -> sprintf "(%s == %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Neq, [v1; v2] -> (
        match (cval_ctyp v1, cval_ctyp v2) with
        | CT_sbits _, _ -> sprintf "neq_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u320 left || is_c_repr_u320 right ->
            sprintf "(!eq_u320(%s, %s))" (u320_of v1) (u320_of v2)
        | left, right when is_c_repr_u256 left && is_c_repr_u128 right ->
            sprintf "(!u256_eq_u128(%s, %s))" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u128 left && is_c_repr_u256 right ->
            sprintf "(!u256_eq_u128(%s, %s))" (sgen_cval v2) (sgen_cval v1)
        | left, CT_fuint _ when is_c_repr_u128 left -> sprintf "(!u128_eq_u64(%s, %s))" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, right when is_c_repr_u128 right -> sprintf "(!u128_eq_u64(%s, %s))" (sgen_cval v2) (sgen_cval v1)
        | left, CT_fuint _ when is_c_repr_u256 left -> sprintf "(!u256_eq_u64(%s, %s))" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, right when is_c_repr_u256 right -> sprintf "(!u256_eq_u64(%s, %s))" (sgen_cval v2) (sgen_cval v1)
        | ctyp, _ when is_c_repr_value ctyp ->
            sprintf "(!eq_%s(%s, %s))" (sgen_ctyp_name ctyp) (sgen_cval v1) (sgen_cval v2)
        | _ -> sprintf "(%s != %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Ilt, [v1; v2] when is_c_repr_u320 (cval_ctyp v1) || is_c_repr_u320 (cval_ctyp v2) ->
        sprintf "u320_lt(%s, %s)" (u320_of v1) (u320_of v2)
    | Ilt, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) && is_c_repr_u128 (cval_ctyp v2) ->
        sprintf "u256_lt_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilt, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) && is_c_repr_u256 (cval_ctyp v2) ->
        sprintf "u128_lt_u256(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilt, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u128_lt_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilt, [v1; v2] when (match cval_ctyp v1 with CT_fuint _ -> true | _ -> false) && is_c_repr_u128 (cval_ctyp v2) ->
        sprintf "u64_lt_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilt, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) -> sprintf "u128_lt(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilt, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u256_lt_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilt, [v1; v2] when (match cval_ctyp v1 with CT_fuint _ -> true | _ -> false) && is_c_repr_u256 (cval_ctyp v2) ->
        sprintf "u64_lt_u256(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilt, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) -> sprintf "u256_lt(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilt, [v1; v2] -> sprintf "(%s < %s)" (sgen_cval v1) (sgen_cval v2)
    | Igt, [v1; v2] -> sgen_call Ilt [v2; v1]
    | Ilteq, [v1; v2] -> sprintf "(!%s)" (sgen_call Ilt [v2; v1])
    | Igteq, [v1; v2] -> sprintf "(!%s)" (sgen_call Ilt [v1; v2])
    | Widening_iadd (128, _), [v1; v2] -> sprintf "u128_add_u64_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Widening_imul (128, _), [v1; v2] -> sprintf "u128_mul_u64_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Widening_iadd (256, _), [v1; v2] -> (
        match (cval_ctyp v1, cval_ctyp v2) with
        | left, right when is_c_repr_u128 left && is_c_repr_u128 right ->
            sprintf "u256_add_u128_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, CT_fuint _ when is_c_repr_u128 left -> sprintf "u256_add_u128_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, right when is_c_repr_u128 right ->
            sprintf "u256_add_u64_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right ->
            failwith
              (sprintf "Unsupported exact widening addition carriers %s and %s" (string_of_ctyp left)
                 (string_of_ctyp right)
              )
      )
    | Widening_imul (256, _), [v1; v2] -> (
        match (cval_ctyp v1, cval_ctyp v2) with
        | left, right when is_c_repr_u128 left && is_c_repr_u128 right ->
            sprintf "u256_mul_u128_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, CT_fuint _ when is_c_repr_u128 left -> sprintf "u256_mul_u128_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, right when is_c_repr_u128 right ->
            sprintf "u256_mul_u64_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right ->
            failwith
              (sprintf "Unsupported exact widening multiplication carriers %s and %s" (string_of_ctyp left)
                 (string_of_ctyp right)
              )
      )
    | Widening_iadd (320, _), [v1; v2] -> sprintf "u320_add_widen(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Widening_imul (320, _), [v1; v2] -> sprintf "u320_mul_widen(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | (Widening_iadd (width, _) | Widening_imul (width, _)), _ ->
        failwith (sprintf "Unsupported exact widening integer operation at width %d" width)
    | Wrapping_iadd width, [v1; v2] -> (
        match cval_ctyp v1 with
        | ctyp when is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp -> sgen_call Iadd [v1; v2]
        | CT_fuint _ ->
            let arithmetic_width = if width <= 16 then 32 else width in
            sprintf "((uint%d_t)(((uint%d_t)%s) + ((uint%d_t)%s)))" width arithmetic_width (sgen_cval v1)
              arithmetic_width (sgen_cval v2)
        | ctyp -> failwith (sprintf "Unsupported wrapping addition carrier %s" (string_of_ctyp ctyp))
      )
    | Wrapping_isub width, [v1; v2] -> (
        match cval_ctyp v1 with
        | ctyp when is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp -> sgen_call Isub [v1; v2]
        | CT_fuint _ ->
            let arithmetic_width = if width <= 16 then 32 else width in
            sprintf "((uint%d_t)(((uint%d_t)%s) - ((uint%d_t)%s)))" width arithmetic_width (sgen_cval v1)
              arithmetic_width (sgen_cval v2)
        | ctyp -> failwith (sprintf "Unsupported wrapping subtraction carrier %s" (string_of_ctyp ctyp))
      )
    | Wrapping_imul width, [v1; v2] -> (
        match cval_ctyp v1 with
        | ctyp when is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp -> sgen_call Imul [v1; v2]
        | CT_fuint _ ->
            let arithmetic_width = if width <= 16 then 32 else width in
            sprintf "((uint%d_t)(((uint%d_t)%s) * ((uint%d_t)%s)))" width arithmetic_width (sgen_cval v1)
              arithmetic_width (sgen_cval v2)
        | ctyp -> failwith (sprintf "Unsupported wrapping multiplication carrier %s" (string_of_ctyp ctyp))
      )
    | Iadd, [v1; v2] -> (
        match (cval_ctyp v1, cval_ctyp v2) with
        | left, right when is_c_repr_u320 left || is_c_repr_u320 right ->
            sprintf "u320_add(%s, %s)" (u320_of v1) (u320_of v2)
        | left, right when is_c_repr_u256 left && is_c_repr_u128 right ->
            sprintf "u256_add_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u128 left && is_c_repr_u256 right ->
            sprintf "u256_add_u128(%s, %s)" (sgen_cval v2) (sgen_cval v1)
        | left, CT_fuint _ when is_c_repr_u128 left -> sprintf "u128_add_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u128 left && is_c_repr_u128 right ->
            sprintf "u128_add(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, CT_fuint _ when is_c_repr_u256 left -> sprintf "u256_add_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u256 left && is_c_repr_u256 right ->
            sprintf "u256_add(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, _ | CT_fint _, _ ->
            failwith
              (sprintf "Unproved fixed-width integer addition reached C code generation: %s:%s + %s:%s" (sgen_cval v1)
                 (string_of_ctyp (cval_ctyp v1))
                 (sgen_cval v2)
                 (string_of_ctyp (cval_ctyp v2))
              )
        | _ -> sprintf "(%s + %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Proven_iadd, [v1; v2] -> sgen_proven_native_binop "+" v1 v2
    | Proven_isub, [v1; v2] -> sgen_proven_native_binop "-" v1 v2
    | Proven_imul, [v1; v2] -> sgen_proven_native_binop "*" v1 v2
    | Proven_idiv, [v1; v2] -> sgen_proven_native_binop "/" v1 v2
    | Proven_imod, [v1; v2] -> sgen_proven_native_binop "%" v1 v2
    | Isub, [v1; v2] -> (
        match (cval_ctyp v1, cval_ctyp v2) with
        | left, right when is_c_repr_u320 left && is_c_repr_u320 right ->
            sprintf "u320_sub(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u320 left -> sprintf "u320_sub(%s, %s)" (sgen_cval v1) (u320_of v2)
        | left, right when is_c_repr_u256 left && is_c_repr_u320 right ->
            sprintf "u256_sub_u320(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u128 left && is_c_repr_u320 right ->
            sprintf "u128_sub_u320(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, right when is_c_repr_u320 right -> sprintf "u64_sub_u320(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u256 left && is_c_repr_u128 right ->
            sprintf "u256_sub_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u128 left && is_c_repr_u256 right ->
            sprintf "u128_sub_u256(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, CT_fuint _ when is_c_repr_u128 left -> sprintf "u128_sub_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, right when is_c_repr_u128 right -> sprintf "u64_sub_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u128 left && is_c_repr_u128 right ->
            sprintf "u128_sub(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, CT_fuint _ when is_c_repr_u256 left -> sprintf "u256_sub_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, right when is_c_repr_u256 right -> sprintf "u64_sub_u256(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | left, right when is_c_repr_u256 left && is_c_repr_u256 right ->
            sprintf "u256_sub(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _, _ | CT_fint _, _ ->
            failwith
              (sprintf "Unproved fixed-width integer subtraction reached C code generation: %s:%s - %s:%s" (sgen_cval v1)
                 (string_of_ctyp (cval_ctyp v1))
                 (sgen_cval v2)
                 (string_of_ctyp (cval_ctyp v2))
              )
        | _ -> sprintf "(%s - %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Imul, [v1; v2] when is_c_repr_u320 (cval_ctyp v1) || is_c_repr_u320 (cval_ctyp v2) ->
        sprintf "u320_mul(%s, %s)" (u320_of v1) (u320_of v2)
    | Imul, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) && is_c_repr_u128 (cval_ctyp v2) ->
        sprintf "u256_mul_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imul, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) && is_c_repr_u256 (cval_ctyp v2) ->
        sprintf "u256_mul_u128(%s, %s)" (sgen_cval v2) (sgen_cval v1)
    | Imul, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u128_mul_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imul, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) -> sprintf "u128_mul(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imul, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u256_mul_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imul, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) -> sprintf "u256_mul(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imul, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fuint _ | CT_fint _ ->
            failwith
              (sprintf "Unproved fixed-width integer multiplication reached C code generation: %s:%s * %s:%s"
                 (sgen_cval v1)
                 (string_of_ctyp (cval_ctyp v1))
                 (sgen_cval v2)
                 (string_of_ctyp (cval_ctyp v2))
              )
        | _ -> sprintf "(%s * %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Idiv, [v1; v2] when is_c_repr_u320 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u320_div_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Idiv, [v1; v2] when is_c_repr_u320 (cval_ctyp v1) -> sprintf "u320_div(%s, %s)" (sgen_cval v1) (u320_of v2)
    | Idiv, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) && is_c_repr_u128 (cval_ctyp v2) ->
        sprintf "u256_div_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Idiv, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) && is_c_repr_u256 (cval_ctyp v2) ->
        sprintf "u128_div_u256(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Idiv, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u128_div_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Idiv, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) -> sprintf "u128_div(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Idiv, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u256_div_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Idiv, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) -> sprintf "u256_div(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Idiv, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fuint _ | CT_fint _ ->
            failwith
              (sprintf "Unproved fixed-width integer division reached C code generation: %s:%s / %s:%s" (sgen_cval v1)
                 (string_of_ctyp (cval_ctyp v1))
                 (sgen_cval v2)
                 (string_of_ctyp (cval_ctyp v2))
              )
        | _ -> sprintf "(%s / %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Imod, [v1; v2] when is_c_repr_u320 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u320_mod_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imod, [v1; v2] when is_c_repr_u320 (cval_ctyp v1) -> sprintf "u320_mod(%s, %s)" (sgen_cval v1) (u320_of v2)
    | Imod, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) && is_c_repr_u128 (cval_ctyp v2) ->
        sprintf "u256_mod_u128(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imod, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) && is_c_repr_u256 (cval_ctyp v2) ->
        sprintf "u128_mod_u256(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imod, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u128_mod_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imod, [v1; v2] when is_c_repr_u128 (cval_ctyp v1) -> sprintf "u128_mod(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imod, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) && match cval_ctyp v2 with CT_fuint _ -> true | _ -> false ->
        sprintf "u256_mod_u64(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imod, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) -> sprintf "u256_mod(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imod, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fuint _ | CT_fint _ ->
            failwith
              (sprintf "Unproved fixed-width integer modulo reached C code generation: %s:%s %% %s:%s" (sgen_cval v1)
                 (string_of_ctyp (cval_ctyp v1))
                 (sgen_cval v2)
                 (string_of_ctyp (cval_ctyp v2))
              )
        | _ -> sprintf "(%s %% %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Power_of_two_idiv exponent, [value] -> (
        match cval_ctyp value with
        | CT_fint _ | CT_fuint _ ->
            if exponent = 0 then sgen_cval value else sprintf "(%s >> %d)" (sgen_cval value) exponent
        | ctyp ->
            c_error (sprintf "Cannot lower proved power-of-two division for %s" (string_of_ctyp ctyp))
      )
    | Power_of_two_imod exponent, [value] -> (
        match cval_ctyp value with
        | CT_fint _ | CT_fuint _ ->
            let mask = Big_int.pred (Big_int.pow_int_positive 2 exponent) in
            sprintf "(%s & %s)" (sgen_cval value) (sgen_cval (V_lit (VL_int mask, cval_ctyp value)))
        | ctyp ->
            c_error (sprintf "Cannot lower proved power-of-two remainder for %s" (string_of_ctyp ctyp))
      )
    | (Mixed_proven_idiv (operation_ctyp, result_ctyp) | Mixed_proven_imod (operation_ctyp, result_ctyp)), [left; right] -> (
        (match (operation_ctyp, cval_ctyp left, cval_ctyp right) with
        | (CT_fint _ | CT_fuint _), (CT_fint _ | CT_fuint _), (CT_fint _ | CT_fuint _) -> ()
        | operation_ctyp, left_ctyp, right_ctyp ->
            c_error
              (sprintf "Cannot lower mixed proved division with %s for %s and %s" (string_of_ctyp operation_ctyp)
                 (string_of_ctyp left_ctyp) (string_of_ctyp right_ctyp)
              ));
        let operator = match op with Mixed_proven_idiv _ -> "/" | _ -> "%" in
        sprintf "((%s)(((%s)%s) %s ((%s)%s)))" (sgen_ctyp result_ctyp) (sgen_ctyp operation_ctyp)
          (sgen_cval left) operator (sgen_ctyp operation_ctyp) (sgen_cval right)
      )
    | Unsigned width, [vec] -> sprintf "((%s) %s)" (sgen_ctyp (CT_fuint width)) (sgen_cval vec)
    | Signed 64, [vec] -> (
        match cval_ctyp vec with CT_fbits n -> sprintf "fast_signed(%s, %d)" (sgen_cval vec) n | _ -> assert false
      )
    | Bvand, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fbits _ -> sprintf "(%s & %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _ -> sprintf "(%s & %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_sbits _ -> sprintf "and_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u128 ctyp -> sprintf "u128_and(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_and(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp ->
            c_error
              (sprintf "Cannot lower bitwise and for %s: %s" (string_of_ctyp ctyp)
                 (Jib_util.string_of_cval (V_call (Bvand, [v1; v2])))
              )
      )
    | Bvnot, [v] -> (
        match cval_ctyp v with
        | CT_fbits n -> sprintf "(~(%s) & %s)" (sgen_cval v) (sgen_cval (v_mask_lower n))
        | CT_sbits _ -> sprintf "not_sbits(%s)" (sgen_cval v)
        | ctyp when is_c_repr_u128 ctyp -> sprintf "u128_not(%s)" (sgen_cval v)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_not(%s)" (sgen_cval v)
        | _ -> assert false
      )
    | Bvor, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fbits _ -> sprintf "(%s | %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _ -> sprintf "(%s | %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_sbits _ -> sprintf "or_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u128 ctyp -> sprintf "u128_or(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_or(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> assert false
      )
    | Bvxor, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fbits _ -> sprintf "(%s ^ %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fuint _ -> sprintf "(%s ^ %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_sbits _ -> sprintf "xor_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u128 ctyp -> sprintf "u128_xor(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_xor(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> assert false
      )
    | Bvadd, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fbits n -> sprintf "((%s + %s) & %s)" (sgen_cval v1) (sgen_cval v2) (sgen_cval (v_mask_lower n))
        | CT_sbits _ -> sprintf "add_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_add(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> assert false
      )
    | Bvsub, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fbits n -> sprintf "((%s - %s) & %s)" (sgen_cval v1) (sgen_cval v2) (sgen_cval (v_mask_lower n))
        | CT_sbits _ -> sprintf "sub_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_sub(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> assert false
      )
    | Bvshiftl, [value; amount] -> (
        match cval_ctyp value with
        | CT_fbits width ->
            sprintf "((%s >= UINT64_C(64)) ? UINT64_C(0) : ((%s << %s) & %s))" (sgen_cval amount) (sgen_cval value)
              (sgen_cval amount) (sgen_mask width)
        | _ -> assert false
      )
    | Bvshiftr, [value; amount] -> (
        match cval_ctyp value with
        | CT_fbits _ -> sprintf "safe_rshift(%s, %s)" (sgen_cval value) (sgen_cval amount)
        | _ -> assert false
      )
    | Proven_bvshiftl 64, [value; amount] -> (
        match cval_ctyp value with
        | CT_fbits width ->
            sprintf "((%s << %s) & %s)" (sgen_cval value) (sgen_cval amount) (sgen_mask width)
        | _ -> assert false
      )
    | Proven_bvshiftr 64, [value; amount] -> (
        match cval_ctyp value with
        | CT_fbits _ -> sprintf "(%s >> %s)" (sgen_cval value) (sgen_cval amount)
        | _ -> assert false
      )
    | Proven_bvarith_shiftr 64, [value; amount] -> (
        match cval_ctyp value with
        | CT_fbits width ->
            let mask = sgen_mask width in
            let sign = sprintf "((%s >> %d) & UINT64_C(1))" (sgen_cval value) (width - 1) in
            sprintf "((%s >> %s) | (%s ? (%s ^ (%s >> %s)) : UINT64_C(0)))" (sgen_cval value)
              (sgen_cval amount) sign mask mask (sgen_cval amount)
        | _ -> assert false
      )
    | (Proven_bvshiftl _ | Proven_bvshiftr _ | Proven_bvarith_shiftr _), _ -> assert false
    | Bvrotr (width, amount), [value]
      when 0 < width && width <= 64 && 0 < amount && amount < width -> (
        match cval_ctyp value with
        | CT_fbits source_width when width <= source_width ->
            let masked = sprintf "(%s & %s)" (sgen_cval value) (sgen_mask width) in
            sprintf "(((%s >> %d) | (%s << %d)) & %s)" masked amount masked (width - amount)
              (sgen_mask width)
        | _ -> assert false
      )
    | Bvrotr _, _ -> assert false
    | Bvarith_shiftr, [value; amount] -> (
        match cval_ctyp value with
        | CT_fbits width ->
            let mask = sgen_mask width in
            let sign = sprintf "((%s >> %d) & UINT64_C(1))" (sgen_cval value) (width - 1) in
            sprintf
              "((%s >= UINT64_C(%d)) ? (%s ? %s : UINT64_C(0)) : (safe_rshift(%s, %s) | (%s ? (%s ^ safe_rshift(%s, \
               %s)) : UINT64_C(0))))"
              (sgen_cval amount) width sign mask (sgen_cval value) (sgen_cval amount) sign mask mask (sgen_cval amount)
        | _ -> assert false
      )
    | Bvaccess, [vec; n] -> (
        match cval_ctyp vec with
        | CT_fbits _ -> sprintf "(UINT64_C(1) & (%s >> %s))" (sgen_cval vec) (sgen_cval n)
        | CT_sbits _ -> sprintf "(UINT64_C(1) & (%s.bits >> %s))" (sgen_cval vec) (sgen_cval n)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_bit(%s, %s)" (sgen_cval vec) (sgen_cval n)
        | _ -> assert false
      )
    | Slice len, [vec; start] -> (
        match cval_ctyp vec with
        | CT_fbits _ ->
            sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & safe_rshift(%s, %s))" len (sgen_cval vec)
              (sgen_cval start)
        | CT_fuint _ ->
            sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & safe_rshift(%s, %s))" len (sgen_cval vec) (sgen_cval start)
        | CT_sbits _ ->
            sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & safe_rshift(%s.bits, %s))" len (sgen_cval vec)
              (sgen_cval start)
        | ctyp when is_c_repr_u128 ctyp ->
            let extracted = sprintf "u128_extract_u64(%s, (uint64_t)(%s))" (sgen_cval vec) (sgen_cval start) in
            if len = 64 then extracted else sprintf "(%s & %s)" (sgen_mask len) extracted
        | ctyp when is_c_repr_u256 ctyp ->
            let extracted = sprintf "u256_extract_u64(%s, (uint64_t)(%s))" (sgen_cval vec) (sgen_cval start) in
            if len = 64 then extracted else sprintf "(%s & %s)" (sgen_mask len) extracted
        | _ -> assert false
      )
    | Proven_slice (len, 64), [vec; start] -> (
        let extracted =
          match cval_ctyp vec with
          | CT_fbits _ | CT_fuint _ -> sprintf "(%s >> %s)" (sgen_cval vec) (sgen_cval start)
          | CT_sbits _ -> sprintf "(%s.bits >> %s)" (sgen_cval vec) (sgen_cval start)
          | _ -> assert false
        in
        if len = 64 then extracted else sprintf "(%s & %s)" (sgen_mask len) extracted
      )
    | Proven_slice _, _ -> assert false
    | Sslice 64, [vec; start; len] -> (
        match cval_ctyp vec with
        | CT_fbits _ -> sprintf "sslice(%s, %s, %s)" (sgen_cval vec) (sgen_cval start) (sgen_cval len)
        | CT_sbits _ -> sprintf "sslice(%s.bits, %s, %s)" (sgen_cval vec) (sgen_cval start) (sgen_cval len)
        | _ -> assert false
      )
    | Set_slice, [vec; start; slice] -> (
        match (cval_ctyp vec, cval_ctyp slice) with
        | CT_fbits _, CT_fbits 0 -> sgen_cval vec
        | CT_fbits _, CT_fbits m ->
            sprintf "((%s & ~(%s << %s)) | (%s << %s))" (sgen_cval vec) (sgen_mask m) (sgen_cval start)
              (sgen_cval slice) (sgen_cval start)
        | _ -> assert false
      )
    | Zero_extend n, [v] -> (
        match cval_ctyp v with
        | CT_fbits _ -> sgen_cval v
        | CT_sbits _ -> sprintf "fast_zero_extend(%s, %d)" (sgen_cval v) n
        | _ -> assert false
      )
    | Sign_extend n, [v] -> (
        match cval_ctyp v with
        | CT_fbits m -> sprintf "fast_sign_extend(%s, %d, %d)" (sgen_cval v) m n
        | CT_sbits _ -> sprintf "fast_sign_extend2(%s, %d)" (sgen_cval v) n
        | _ -> assert false
      )
    | Replicate n, [v] -> (
        match cval_ctyp v with
        | CT_fbits m -> sprintf "fast_replicate_bits(UINT64_C(%d), %s, %d)" m (sgen_cval v) n
        | _ -> assert false
      )
    | Concat, [v1; v2] -> (
        (* Optimized routines for all combinations of fixed and small bits
           appends, where the result is guaranteed to be smaller than 64. *)
        match (cval_ctyp v1, cval_ctyp v2) with
        | CT_fbits 0, CT_fbits _ -> sgen_cval v2
        | CT_fbits _, CT_fbits n2 -> sprintf "(%s << %d) | %s" (sgen_cval v1) n2 (sgen_cval v2)
        | CT_sbits 64, CT_fbits n2 -> sprintf "append_sf(%s, %s, %d)" (sgen_cval v1) (sgen_cval v2) n2
        | CT_fbits n1, CT_sbits 64 -> sprintf "append_fs(%s, %d, %s)" (sgen_cval v1) n1 (sgen_cval v2)
        | CT_sbits 64, CT_sbits 64 -> sprintf "append_ss(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> assert false
      )
    | Ite, [i; t; e] -> sprintf "(%s ? %s : %s)" (sgen_cval i) (sgen_cval t) (sgen_cval e)
    | String_eq, [s1; s2] -> sprintf "(strcmp(%s, %s) == 0)" (sgen_cval s1) (sgen_cval s2)
    | _, _ -> failwith "Could not generate cval primop"

  let sgen_cval_param cval =
    match cval_ctyp cval with
    | CT_lbits -> sgen_cval cval ^ ", " ^ string_of_bool true
    | CT_sbits _ -> sgen_cval cval ^ ", " ^ string_of_bool true
    | CT_fbits len -> sgen_cval cval ^ ", UINT64_C(" ^ string_of_int len ^ ") , " ^ string_of_bool true
    | _ -> sgen_cval cval

  let rec sgen_clexp l = function
    | CL_id (Have_exception _, _) -> "have_exception"
    | CL_id (Current_exception _, _) -> if Config.optimized_model then "&current_exception" else "current_exception"
    | CL_id (Throw_location _, _) -> "throw_location"
    | CL_id (Memory_writes _, _) -> "memory_writes"
    | CL_id (Channel _, _) -> Reporting.unreachable l __POS__ "CL_id Channel should not appear in C backend"
    | CL_id (Return _, _) -> Reporting.unreachable l __POS__ "CL_id Return should have been removed"
    | CL_id (name, _) -> "&" ^ sgen_name name
    | CL_field (clexp, field, _) -> "&((" ^ sgen_clexp l clexp ^ ")->" ^ sgen_id field ^ ")"
    | CL_tuple (clexp, n) -> sprintf "&((%s)->%s)" (sgen_clexp l clexp) (sgen_tuple_id n)
    | CL_addr clexp -> "(*(" ^ sgen_clexp l clexp ^ "))"
    | CL_void _ -> assert false
    | CL_rmw _ -> assert false

  let rec sgen_clexp_pure l = function
    | CL_id (Have_exception _, _) -> "have_exception"
    | CL_id (Current_exception _, _) -> "current_exception"
    | CL_id (Throw_location _, _) -> "throw_location"
    | CL_id (Memory_writes _, _) -> "memory_writes"
    | CL_id (Channel _, _) -> Reporting.unreachable l __POS__ "CL_id Channel should not appear in C backend"
    | CL_id (Return _, _) -> Reporting.unreachable l __POS__ "CL_id Return should have been removed"
    | CL_id (name, _) -> sgen_name name
    | CL_field (clexp, field, _) -> sgen_clexp_pure l clexp ^ "." ^ sgen_id field
    | CL_tuple (clexp, n) -> sgen_clexp_pure l clexp ^ "." ^ sgen_tuple_id n
    | CL_addr clexp -> "(*(" ^ sgen_clexp_pure l clexp ^ "))"
    | CL_void _ -> assert false
    | CL_rmw _ -> assert false

  let codegen_equal ctyp arg1 arg2 =
    match ctyp with
    | CT_ref _ -> ksprintf string "(%s == %s)" arg1 arg2
    | CT_fint _ | CT_fuint _ -> ksprintf string "(%s == %s)" arg1 arg2
    | ctyp -> sail_equal (sgen_ctyp_name ctyp) "%s, %s" arg1 arg2

  let monomorphic_id_base id =
    let name = string_of_id id in
    match String.index_opt name '<' with Some i -> String.sub name 0 i | None -> name

  let matching_variant_constructors l ctx ctyp_to ctyp_from =
    let variant_to, constructors_to = variant_constructor_bindings l ctx ctyp_to in
    let variant_from, constructors_from = variant_constructor_bindings l ctx ctyp_from in
    if monomorphic_id_base variant_to <> monomorphic_id_base variant_from then None
    else (
      let constructors_from = Bindings.bindings constructors_from in
      let find_source_constructor constructor_to =
        let base = monomorphic_id_base constructor_to in
        List.find_opt (fun (constructor_from, _) -> monomorphic_id_base constructor_from = base) constructors_from
      in
      let constructors =
        Bindings.bindings constructors_to
        |> List.map (fun (constructor_to, ctyp_to) ->
            match find_source_constructor constructor_to with
            | Some (constructor_from, ctyp_from) -> (constructor_to, ctyp_to, constructor_from, ctyp_from)
            | None ->
                Reporting.unreachable l __POS__
                  (Printf.sprintf "Could not match constructor %s while converting %s to %s"
                     (string_of_id constructor_to) (string_of_ctyp ctyp_from) (string_of_ctyp ctyp_to)
                  )
        )
      in
      if List.length constructors = List.length constructors_from then Some constructors
      else
        Reporting.unreachable l __POS__
          (Printf.sprintf "Mismatched constructors while converting %s to %s" (string_of_ctyp ctyp_from)
             (string_of_ctyp ctyp_to)
          )
    )

  let codegen_fixed_integer_conversion l clexp ctyp_to cval ctyp_from =
    let storage_width width = if width > 64 then 128 else native_c_integer_width width in
    let assignment =
      ksprintf string "  %s = (%s)(%s);" (sgen_clexp_pure l clexp) (sgen_ctyp ctyp_to) (sgen_cval cval)
    in
    let failure message = ksprintf string "    sail_native_conversion_failure(\"%s\");" message in
    let checked condition message =
      ksprintf string "  if (%s) {" condition ^^ hardline ^^ failure message ^^ hardline ^^ string "  }" ^^ hardline
    in
    let lower_bound ctyp width = sgen_value ctyp (VL_int (min_int width)) in
    let upper_signed_bound ctyp width = sgen_value ctyp (VL_int (max_int width)) in
    let upper_unsigned_bound ctyp width = sgen_value ctyp (VL_int (max_uint width)) in
    let outside_target_domain () = sprintf "integer value is outside the %s domain" (sgen_ctyp ctyp_to) in
    let negative_target () = sprintf "negative integer cannot be represented as %s" (sgen_ctyp ctyp_to) in
    match (ctyp_to, ctyp_from) with
    | CT_fuint to_width, CT_fuint from_width ->
        let to_width = storage_width to_width in
        let from_width = storage_width from_width in
        if from_width <= to_width then assignment
        else
          checked (sprintf "%s > %s" (sgen_cval cval) (upper_unsigned_bound ctyp_to to_width)) (outside_target_domain ())
          ^^ assignment
    | CT_fint to_width, CT_fint from_width ->
        let to_width = storage_width to_width in
        let from_width = storage_width from_width in
        if from_width <= to_width then assignment
        else
          checked
            (sprintf "%s < %s || %s > %s" (sgen_cval cval) (lower_bound ctyp_to to_width) (sgen_cval cval)
               (upper_signed_bound ctyp_to to_width)
            )
            (outside_target_domain ())
          ^^ assignment
    | CT_fuint to_width, CT_fint from_width ->
        let to_width = storage_width to_width in
        let from_width = storage_width from_width in
        let negative = checked (sprintf "%s < 0" (sgen_cval cval)) (negative_target ()) in
        if from_width <= to_width then negative ^^ assignment
        else
          negative
          ^^ checked
               (sprintf "%s > %s" (sgen_cval cval) (upper_unsigned_bound ctyp_to to_width))
               (outside_target_domain ())
          ^^ assignment
    | CT_fint to_width, CT_fuint from_width ->
        let to_width = storage_width to_width in
        let from_width = storage_width from_width in
        if from_width < to_width then assignment
        else
          checked (sprintf "%s > %s" (sgen_cval cval) (upper_signed_bound ctyp_to to_width)) (outside_target_domain ())
          ^^ assignment
    | _ -> assert false

  (** Generate instructions to copy from a cval to a clexp. This will insert any needed type conversions from big
      integers to small integers (or vice versa), or from arbitrary-length bitvectors to and from uint64 bitvectors as
      needed. *)
  let rec codegen_conversion l ctx clexp cval =
    let ctyp_to = clexp_ctyp clexp in
    let ctyp_from = cval_ctyp cval in
    match (ctyp_to, ctyp_from) with
    (* When both types are equal, we don't need any conversion. *)
    | _, _ when ctyp_equal ctyp_to ctyp_from ->
        if is_stack_ctyp ctx ctyp_to then ksprintf string "  %s = %s;" (sgen_clexp_pure l clexp) (sgen_cval cval)
        else sail_copy ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) "%s, %s" (sgen_clexp l clexp) (sgen_cval cval)
    | (CT_fint _ | CT_fuint _), (CT_fint _ | CT_fuint _) ->
        (* Most width changes are proved refinements selected from semantic
           ranges.  Explicit [$[c_repr]] newtypes are also represented by this
           path, however, and their constructors are genuine runtime
           boundaries.  Retain checks whenever the source C carrier is not a
           subset of the destination carrier; no arbitrary-precision integer
           is needed to enforce those bounds. *)
        codegen_fixed_integer_conversion l clexp ctyp_to cval ctyp_from
    | CT_lint, from_typ when is_c_repr_u320 from_typ ->
        ksprintf string "  u320_unsigned(%s, %s);" (sgen_clexp l clexp) (sgen_cval cval)
    | to_typ, CT_lint when is_c_repr_u320 to_typ ->
        ksprintf string "  %s = u320_of_sail_int(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, CT_fuint _ when is_c_repr_u320 to_typ ->
        ksprintf string "  %s = u320_of_u64(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, from_typ when is_c_repr_u320 to_typ && is_c_repr_u128 from_typ ->
        ksprintf string "  %s = u320_of_u128(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, from_typ when is_c_repr_u320 to_typ && is_c_repr_u256 from_typ ->
        ksprintf string "  %s = u320_of_u256(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | CT_fuint _, from_typ when is_c_repr_u320 from_typ ->
        ksprintf string "  %s = u320_to_u64(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, from_typ when is_c_repr_u256 to_typ && is_c_repr_u320 from_typ ->
        ksprintf string "  %s = u256_of_u320(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, from_typ when is_c_repr_u128 to_typ && is_c_repr_u320 from_typ ->
        ksprintf string "  %s = u128_of_u320(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, CT_lbits when is_c_repr_u256 to_typ ->
        ksprintf string "  %s = u256_of_lbits(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | CT_lbits, from_typ when is_c_repr_u256 from_typ ->
        ksprintf string "  lbits_of_u256(%s, %s);" (sgen_clexp l clexp) (sgen_cval cval)
    | CT_lint, from_typ when is_c_repr_u256 from_typ ->
        ksprintf string "  u256_unsigned(%s, %s);" (sgen_clexp l clexp) (sgen_cval cval)
    | CT_lint, from_typ when is_c_repr_u128 from_typ ->
        ksprintf string "  u128_unsigned(%s, %s);" (sgen_clexp l clexp) (sgen_cval cval)
    | CT_lint, CT_fint width when width > 64 ->
        let limbs = ngensym () in
        ksprintf string "  {" ^^ hardline
        ^^ ksprintf string "    const uint64_t %s[2] = {(uint64_t)(%s)," (sgen_name limbs) (sgen_cval cval)
        ^^ hardline
        ^^ ksprintf string "      (uint64_t)(((unsigned __int128)(%s)) >> 64)};" (sgen_cval cval)
        ^^ hardline
        ^^ ksprintf string "    sail_int_from_twos_complement_u64_array(%s, %s, 2);" (sgen_clexp l clexp)
             (sgen_name limbs)
        ^^ hardline ^^ string "  }"
    | to_typ, CT_lint when is_c_repr_u256 to_typ ->
        ksprintf string "  %s = u256_of_sail_int(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, CT_fbits _ when is_c_repr_u256 to_typ ->
        ksprintf string "  %s = u256_of_fbits(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, CT_fuint _ when is_c_repr_u256 to_typ ->
        ksprintf string "  %s = u256_of_fbits(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, from_typ when is_c_repr_u256 to_typ && is_c_repr_u128 from_typ ->
        ksprintf string "  %s = u256_of_u128(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | CT_fuint _, from_typ when is_c_repr_u256 from_typ ->
        ksprintf string "  %s = u256_to_u64(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, CT_fuint _ when is_c_repr_u128 to_typ ->
        ksprintf string "  %s = u128_of_u64(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, CT_fint width when is_c_repr_u128 to_typ && width > 64 ->
        ksprintf string "  %s = ((sail_u128){{(uint64_t)(%s), (uint64_t)(((unsigned __int128)(%s)) >> 64)}});"
          (sgen_clexp_pure l clexp) (sgen_cval cval) (sgen_cval cval)
    | to_typ, CT_lint when is_c_repr_u128 to_typ ->
        ksprintf string "  %s = u128_of_sail_int(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | CT_fuint _, from_typ when is_c_repr_u128 from_typ ->
        ksprintf string "  %s = u128_to_u64(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, from_typ when is_c_repr_u128 to_typ && is_c_repr_u256 from_typ ->
        ksprintf string "  %s = u128_of_u256(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)) when is_c_repr_fixed_bytes to_typ ->
        let length = Option.get (c_repr_fixed_bytes_length to_typ) in
        let i = ngensym () in
        ksprintf string "  for (size_t %s = 0; %s < %d; ++%s) {" (sgen_name i) (sgen_name i) length (sgen_name i)
        ^^ hardline
        ^^ ksprintf string "    %s.bytes[%s] = (uint8_t)(%s.data[%s] & UINT64_C(0xff));" (sgen_clexp_pure l clexp)
             (sgen_name i) (sgen_cval cval) (sgen_name i)
        ^^ hardline ^^ string "  }"
    | (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), from_typ when is_c_repr_fixed_bytes from_typ ->
        let length = Option.get (c_repr_fixed_bytes_length from_typ) in
        let i = ngensym () in
        sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) "%s" (sgen_clexp l clexp)
        ^^ hardline
        ^^ ksprintf string "  internal_vector_init_%s(%s, INT64_C(%d));" (sgen_ctyp_name ctyp_to) (sgen_clexp l clexp)
             length
        ^^ hardline
        ^^ ksprintf string "  for (size_t %s = 0; %s < %d; ++%s) {" (sgen_name i) (sgen_name i) length (sgen_name i)
        ^^ hardline
        ^^ ksprintf string "    %s.data[%s] = (uint64_t)%s.bytes[%s];" (sgen_clexp_pure l clexp) (sgen_name i)
             (sgen_cval cval) (sgen_name i)
        ^^ hardline ^^ string "  }"
    | CT_ref _, _ -> codegen_conversion l ctx (CL_addr clexp) cval
    | ( (CT_vector ctyp_elem_to | CT_fvector (_, ctyp_elem_to)),
        (CT_vector ctyp_elem_from | CT_fvector (_, ctyp_elem_from)) ) ->
        let i = ngensym () in
        let from = ngensym () in
        let into = ngensym () in
        sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) "%s" (sgen_clexp l clexp)
        ^^ hardline
        ^^ ksprintf string "  internal_vector_init_%s(%s, %s.len);" (sgen_ctyp_name ctyp_to) (sgen_clexp l clexp)
             (sgen_cval cval)
        ^^ hardline
        ^^ ksprintf string "  for (int %s = 0; %s < %s.len; %s++) {" (sgen_name i) (sgen_name i) (sgen_cval cval)
             (sgen_name i)
        ^^ hardline
        ^^ ( if is_stack_ctyp ctx ctyp_elem_from then
               ksprintf string "    %s %s = %s.data[%s];" (sgen_ctyp ctyp_elem_from) (sgen_name from) (sgen_cval cval)
                 (sgen_name i)
             else
               ksprintf string "    %s %s;" (sgen_ctyp ctyp_elem_from) (sgen_name from)
               ^^ hardline
               ^^ sail_create ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_from) "&%s" (sgen_name from)
               ^^ hardline
               ^^ sail_copy ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_from) "&%s, %s.data[%s]"
                    (sgen_name from) (sgen_cval cval) (sgen_name i)
           )
        ^^ hardline
        ^^ ksprintf string "    %s %s;" (sgen_ctyp ctyp_elem_to) (sgen_name into)
        ^^ ( if is_stack_ctyp ctx ctyp_elem_to then empty
             else hardline ^^ sail_create ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_to) "&%s" (sgen_name into)
           )
        ^^ nest 2 (hardline ^^ codegen_conversion l ctx (CL_id (into, ctyp_elem_to)) (V_id (from, ctyp_elem_from)))
        ^^ hardline
        ^^ ( if is_stack_ctyp ctx ctyp_elem_to then
               ksprintf string "    %s.data[%s] = %s;" (sgen_clexp_pure l clexp) (sgen_name i) (sgen_name into)
             else
               sail_copy ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_to) "&((%s)->data[%s]), %s"
                 (sgen_clexp l clexp) (sgen_name i) (sgen_name into)
               ^^ hardline
               ^^ sail_kill ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_to) "&%s" (sgen_name into)
           )
        ^^ ( if is_stack_ctyp ctx ctyp_elem_from then empty
             else hardline ^^ sail_kill ~prefix:"    " ~suffix:";" (sgen_ctyp_name ctyp_elem_from) "&%s" (sgen_name from)
           )
        ^^ hardline ^^ string "  }"
    | CT_variant _, CT_variant _ -> (
        match matching_variant_constructors l ctx ctyp_to ctyp_from with
        | Some constructors ->
            let source = sgen_cval cval in
            let convert_constructor (constructor_to, payload_to, constructor_from, payload_from) =
              let converted = ngensym () in
              let source_payload = V_ctor_unwrap (cval, (constructor_from, []), payload_from) in
              let declaration =
                ksprintf string "%s %s;" (sgen_ctyp payload_to) (sgen_name converted)
                ^^
                if is_stack_ctyp ctx payload_to then empty
                else hardline ^^ sail_create ~suffix:";" (sgen_ctyp_name payload_to) "&%s" (sgen_name converted)
              in
              let conversion = codegen_conversion l ctx (CL_id (converted, payload_to)) source_payload in
              let construct =
                if Config.optimized_model && is_stack_ctyp ctx ctyp_to then
                  ksprintf string "%s = %s(%s%s);" (sgen_clexp_pure l clexp)
                    (sgen_function_uid (constructor_to, []))
                    (extra_arguments false) (sgen_name converted)
                else
                  ksprintf string "%s(%s%s, %s);"
                    (sgen_function_uid (constructor_to, []))
                    (extra_arguments false) (sgen_clexp l clexp) (sgen_name converted)
              in
              let cleanup =
                if is_stack_ctyp ctx payload_to then empty
                else sail_kill ~suffix:";" (sgen_ctyp_name payload_to) "&%s" (sgen_name converted)
              in
              (ksprintf string "Kind_%s" (sgen_id constructor_from), [declaration; conversion; construct; cleanup])
            in
            c_switch (ksprintf string "(%s.kind)" source) (List.map convert_constructor constructors)
        | None ->
            if is_stack_ctyp ctx ctyp_to then
              sail_convert_of
                ~prefix:(sprintf "  %s = " (sgen_clexp_pure l clexp))
                ~suffix:";" (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from) "%s" (sgen_cval_param cval)
            else
              sail_convert_of ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from) "%s, %s"
                (sgen_clexp l clexp) (sgen_cval_param cval)
      )
    (* If we have to convert between tuple types, convert the fields individually. *)
    | CT_tup ctyps_to, CT_tup ctyps_from when List.length ctyps_to = List.length ctyps_from ->
        let len = List.length ctyps_to in
        let conversions =
          List.mapi
            (fun i _ -> codegen_conversion l ctx (CL_tuple (clexp, i)) (V_tuple_member (cval, len, i)))
            ctyps_from
        in
        string "  /* conversions */" ^^ hardline ^^ separate hardline conversions ^^ hardline
        ^^ string "  /* end conversions */"
    (* For anything not special cased, just try to call a appropriate CONVERT_OF function. *)
    | _, _ when is_stack_ctyp ctx (clexp_ctyp clexp) ->
        sail_convert_of
          ~prefix:(sprintf "  %s = " (sgen_clexp_pure l clexp))
          ~suffix:";" (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from) "%s" (sgen_cval_param cval)
    | _, _ ->
        sail_convert_of ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) (sgen_ctyp_name ctyp_from) "%s, %s"
          (sgen_clexp l clexp) (sgen_cval_param cval)

  (* PPrint doesn't provide a nice way to filter out empty documents *)
  let squash_empty docs = List.filter (fun doc -> requirement doc > 0) docs
  let sq_separate_map sep f xs = separate sep (squash_empty (List.map f xs))

  let rec codegen_instr fid ctx (I_aux (instr, (_, l))) =
    match instr with
    | I_decl (ctyp, id) when is_stack_ctyp ctx ctyp -> ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
    | I_decl (ctyp, id) ->
        ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
        ^^ hardline
        ^^ sail_create ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_copy (clexp, cval) -> codegen_conversion l ctx clexp cval
    | I_jump (cval, label) -> ksprintf string "  if (%s) goto %s;" (sgen_cval cval) label
    | I_if (cval, [], else_instrs) -> codegen_instr fid ctx (iif l (V_call (Bnot, [cval])) else_instrs [])
    | I_if (cval, [then_instr], []) ->
        ksprintf string "  if (%s)" (sgen_cval cval)
        ^^ space
        ^^ surround 2 0 lbrace (codegen_instr fid ctx then_instr) (twice space ^^ rbrace)
    | I_if (cval, then_instrs, []) ->
        string "  if" ^^ space
        ^^ parens (string (sgen_cval cval))
        ^^ space
        ^^ surround 2 0 lbrace (separate_map hardline (codegen_instr fid ctx) then_instrs) (twice space ^^ rbrace)
    | I_if (cval, then_instrs, else_instrs) ->
        let rec codegen_if cval then_instrs else_instrs =
          match else_instrs with
          | [I_aux (I_if (else_i, else_t, else_e), _)] ->
              string "if" ^^ space
              ^^ parens (string (sgen_cval cval))
              ^^ space
              ^^ surround 2 0 lbrace
                   (sq_separate_map hardline (codegen_instr fid ctx) then_instrs)
                   (twice space ^^ rbrace)
              ^^ space ^^ string "else" ^^ space ^^ codegen_if else_i else_t else_e
          | _ ->
              string "if" ^^ space
              ^^ parens (string (sgen_cval cval))
              ^^ space
              ^^ surround 2 0 lbrace
                   (sq_separate_map hardline (codegen_instr fid ctx) then_instrs)
                   (twice space ^^ rbrace)
              ^^ space ^^ string "else" ^^ space
              ^^ surround 2 0 lbrace
                   (sq_separate_map hardline (codegen_instr fid ctx) else_instrs)
                   (twice space ^^ rbrace)
        in
        twice space ^^ codegen_if cval then_instrs else_instrs
    | I_block instrs ->
        string "  {" ^^ jump 2 2 (sq_separate_map hardline (codegen_instr fid ctx) instrs) ^^ hardline ^^ string "  }"
    | I_try_block instrs ->
        string "  { /* try */"
        ^^ jump 2 2 (sq_separate_map hardline (codegen_instr fid ctx) instrs)
        ^^ hardline ^^ string "  }"
    | I_funcall (x, extern_info, f, args) ->
        let special_extern = match extern_info with Extern _ -> true | Call _ -> false in
        let x =
          match x with
          | CR_one x -> x
          | CR_multi _ -> Reporting.unreachable l __POS__ "Multiple returns should not exist in C backend"
        in
        let default_c_args = Util.string_of_list ", " sgen_cval args in
        let ctyp = clexp_ctyp x in
        let is_extern = ctx_is_extern (fst f) ctx || special_extern in
        let fname =
          if special_extern then string_of_id (fst f)
          else if ctx_is_extern (fst f) ctx then ctx_get_extern (fst f) ctx
          else sgen_function_uid f
        in
        let raw_fname = fname in
        let fname =
          match (fname, ctyp) with
          | "__sail_from_bytes_le_fixed_u256", ctyp when is_c_repr_u256 ctyp -> (
              match List.nth_opt args 1 with
              | Some arg -> (
                  match c_repr_fixed_bytes_length (cval_ctyp arg) with
                  | Some length -> sprintf "u256_from_fixed_bytes_%d" length
                  | None -> c_error "native from_bytes_le specialization without fixed-byte argument"
                )
              | None -> c_error "native from_bytes_le specialization without fixed-byte argument"
            )
          | "__sail_to_bytes_le_u256_fixed", ctyp when is_c_repr_fixed_bytes ctyp ->
              sprintf "fixed_bytes_%d_from_u256" (Option.get (c_repr_fixed_bytes_length ctyp))
          | "__sail_u256_addmod", ctyp when is_c_repr_u256 ctyp -> "u256_addmod"
          | "__sail_u256_mulmod", ctyp when is_c_repr_u256 ctyp -> "u256_mulmod"
          | "internal_pick", _ -> sprintf "pick_%s" (sgen_ctyp_name ctyp)
          | "sail_cons", _ -> (
              match Option.map cval_ctyp (List.nth_opt args 0) with
              | Some ctyp -> Util.zencode_string ("cons#" ^ string_of_ctyp (ctyp_suprema_for_c Config.specialize_c ctyp))
              | None -> c_error "cons without specified type"
            )
          | "eq_anything", _ -> (
              match args with
              | cval :: _ -> sprintf "eq_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "eq_anything function with bad arity."
            )
          | "length", _ -> (
              match args with
              | cval :: _ -> sprintf "length_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "length function with bad arity."
            )
          | "vector_access", CT_fbits 1 -> "bitvector_access"
          | "vector_access_inc", CT_fbits 1 -> "bitvector_access_inc"
          | ("vector_access" | "vector_access_inc"), _ -> (
              match args with
              | value :: index :: _
                when (is_c_repr_u256 (cval_ctyp value)
                     || is_c_repr_fixed_bytes (cval_ctyp value)
                     || match cval_ctyp value with CT_vector _ | CT_fvector _ -> true | _ -> false
                     )
                     && is_native_unsigned_integer (cval_ctyp index) ->
                  sprintf "fast_unsigned_vector_access_%s" (sgen_ctyp_name (cval_ctyp value))
              | value :: index :: _
                when (is_c_repr_u256 (cval_ctyp value)
                     || is_c_repr_fixed_bytes (cval_ctyp value)
                     || match cval_ctyp value with CT_vector _ | CT_fvector _ -> true | _ -> false
                     )
                     && is_native_signed_integer (cval_ctyp index) ->
                  sprintf "fast_vector_access_%s" (sgen_ctyp_name (cval_ctyp value))
              | cval :: _ -> sprintf "vector_access_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "vector access function with bad arity."
            )
          | "fast_vector_access", _ -> (
              match args with
              | cval :: _ -> sprintf "fast_vector_access_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "vector access function with bad arity."
            )
          | "fast_unsigned_vector_access", _ -> (
              match args with
              | cval :: _ -> sprintf "fast_unsigned_vector_access_%s" (sgen_ctyp_name (cval_ctyp cval))
              | _ -> c_error "unsigned vector access function with bad arity."
            )
          | "vector_init", ctyp
            when is_c_repr_fixed_bytes ctyp || match ctyp with CT_vector _ | CT_fvector _ -> true | _ -> false -> (
              match List.nth_opt args 0 with
              | Some length when is_native_unsigned_integer (cval_ctyp length) ->
                  sprintf "fast_unsigned_vector_init_%s" (sgen_ctyp_name ctyp)
              | Some length when is_native_signed_integer (cval_ctyp length) ->
                  sprintf "fast_vector_init_%s" (sgen_ctyp_name ctyp)
              | _ -> sprintf "vector_init_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_init", _ -> sprintf "vector_init_%s" (sgen_ctyp_name ctyp)
          | "vector_update_subrange", _ -> sprintf "vector_update_subrange_%s" (sgen_ctyp_name ctyp)
          | "vector_update_subrange_inc", _ -> sprintf "vector_update_subrange_inc_%s" (sgen_ctyp_name ctyp)
          | "vector_subrange", _ -> sprintf "vector_subrange_%s" (sgen_ctyp_name ctyp)
          | "vector_subrange_inc", _ -> sprintf "vector_subrange_inc_%s" (sgen_ctyp_name ctyp)
          | "vector_update", CT_fbits _ -> "update_fbits"
          | "vector_update", CT_lbits -> "update_lbits"
          | "vector_update", ctyp when is_c_repr_u256 ctyp -> (
              match List.nth_opt args 1 with
              | Some index when is_native_unsigned_integer (cval_ctyp index) -> "u256_update_u64"
              | Some index when is_native_signed_integer (cval_ctyp index) -> "u256_update_i64"
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update", ctyp when is_c_repr_fixed_bytes ctyp -> (
              match List.nth_opt args 1 with
              | Some index when is_native_unsigned_integer (cval_ctyp index) ->
                  sprintf "fast_unsigned_vector_update_%s" (sgen_ctyp_name ctyp)
              | Some index when is_native_signed_integer (cval_ctyp index) ->
                  sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update", ((CT_vector _ | CT_fvector _) as ctyp) -> (
              match List.nth_opt args 1 with
              | Some index when is_native_unsigned_integer (cval_ctyp index) ->
                  sprintf "fast_unsigned_vector_update_%s" (sgen_ctyp_name ctyp)
              | Some index when is_native_signed_integer (cval_ctyp index) ->
                  sprintf "fast_vector_update_%s" (sgen_ctyp_name ctyp)
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update", _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
          | "vector_update_inc", CT_fbits _ -> "update_fbits_inc"
          | "vector_update_inc", CT_lbits -> "update_lbits_inc"
          | "vector_update_inc", ctyp when is_c_repr_u256 ctyp -> (
              match List.nth_opt args 1 with
              | Some index when is_native_unsigned_integer (cval_ctyp index) -> "u256_update_u64"
              | Some index when is_native_signed_integer (cval_ctyp index) -> "u256_update_i64"
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update_inc", ctyp when is_c_repr_fixed_bytes ctyp -> (
              match List.nth_opt args 1 with
              | Some index when is_native_unsigned_integer (cval_ctyp index) ->
                  sprintf "fast_unsigned_vector_update_%s" (sgen_ctyp_name ctyp)
              | Some index when is_native_signed_integer (cval_ctyp index) ->
                  sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update_inc", ((CT_vector _ | CT_fvector _) as ctyp) -> (
              match List.nth_opt args 1 with
              | Some index when is_native_unsigned_integer (cval_ctyp index) ->
                  sprintf "fast_unsigned_vector_update_%s" (sgen_ctyp_name ctyp)
              | Some index when is_native_signed_integer (cval_ctyp index) ->
                  sprintf "fast_vector_update_%s" (sgen_ctyp_name ctyp)
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | (("shiftl" | "shiftr" | "arith_shiftr") as shift), ctyp when is_c_repr_u256 ctyp ->
              let suffix =
                match List.nth_opt args 1 with
                | Some amount when is_native_unsigned_integer (cval_ctyp amount) -> "_u64"
                | Some amount when is_native_signed_integer (cval_ctyp amount) -> "_i64"
                | _ -> ""
              in
              "u256_" ^ shift ^ suffix
          | "zero_extend", ctyp when is_c_repr_u256 ctyp -> (
              match List.nth_opt args 0 with
              | Some value when match cval_ctyp value with CT_fbits _ -> true | _ -> false -> "u256_of_fbits"
              | Some value when ctyp_equal (cval_ctyp value) CT_lbits -> "u256_of_lbits"
              | _ -> fname
            )
          | "string_of_bits", _ -> (
              match cval_ctyp (List.nth args 0) with
              | CT_fbits _ -> "string_of_fbits"
              | CT_lbits -> "string_of_lbits"
              | ctyp when is_c_repr_u256 ctyp -> "string_of_u256"
              | _ -> assert false
            )
          | "decimal_string_of_bits", _ -> (
              match cval_ctyp (List.nth args 0) with
              | CT_fbits _ -> "decimal_string_of_fbits"
              | CT_lbits -> "decimal_string_of_lbits"
              | ctyp when is_c_repr_u256 ctyp -> "decimal_string_of_u256"
              | _ -> assert false
            )
          | "sail_unsigned", _ -> (
              match args with cval :: _ when is_c_repr_u256 (cval_ctyp cval) -> "u256_unsigned" | _ -> fname
            )
          | "sail_signed", _ -> (
              match args with cval :: _ when is_c_repr_u256 (cval_ctyp cval) -> "u256_signed" | _ -> fname
            )
          | "internal_vector_update", _ -> sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
          | "internal_vector_init", _ -> sprintf "internal_vector_init_%s" (sgen_ctyp_name ctyp)
          | "undefined_bitvector", ctyp when is_c_repr_u256 ctyp -> "undefined_u256"
          | "undefined_bitvector", CT_fbits _ -> "UNDEFINED(fbits)"
          | "undefined_bitvector", CT_lbits -> "UNDEFINED(lbits)"
          | "undefined_bit", _ -> "UNDEFINED(fbits)"
          | "undefined_vector", _ -> sprintf "UNDEFINED(vector_%s)" (sgen_ctyp_name ctyp)
          | "undefined_list", _ -> sprintf "UNDEFINED(%s)" (sgen_ctyp_name ctyp)
          | fname, _ -> fname
        in
        let c_args =
          match (raw_fname, ctyp, args) with
          | ("__sail_from_bytes_le_fixed_u256" | "__sail_to_bytes_le_u256_fixed"), _, [_; value] -> sgen_cval value
          | "zero_extend", ctyp, value :: _
            when is_c_repr_u256 ctyp && match cval_ctyp value with CT_fbits _ | CT_lbits -> true | _ -> false ->
              sgen_cval value
          | _ -> default_c_args
        in
        if is_extern && raw_fname <> "__sail_fixed_assert" && fname <> "reg_deref" then
          emitted_external_functions := Util.StringSet.add fname !emitted_external_functions;
        if raw_fname = "__sail_fixed_assert" then (
          match args with
          | [condition] ->
              ksprintf string "  if (!(%s)) __builtin_trap();\n  %s = UNIT;" (sgen_cval condition)
                (sgen_clexp_pure l x)
          | _ -> c_error ~loc:l "fixed assertion marker with bad arity"
        )
        else if fname = "reg_deref" then
          if is_stack_ctyp ctx ctyp then ksprintf string "  %s = *(%s);" (sgen_clexp_pure l x) c_args
          else sail_copy ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s, *(%s)" (sgen_clexp_pure l x) c_args
        else if is_stack_ctyp ctx ctyp then
          string (Printf.sprintf "  %s = %s(%s%s);" (sgen_clexp_pure l x) fname (extra_arguments is_extern) c_args)
        else string (Printf.sprintf "  %s(%s%s, %s);" fname (extra_arguments is_extern) (sgen_clexp l x) c_args)
    | I_clear (ctyp, _) when is_stack_ctyp ctx ctyp -> empty
    | I_clear (ctyp, id) -> sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_init (ctyp, id, init) -> (
        match init with
        | Init_cval cval ->
            codegen_instr fid ctx (idecl l ctyp id) ^^ hardline ^^ codegen_conversion l ctx (CL_id (id, ctyp)) cval
        | Init_static VL_undefined -> ksprintf string "  static %s %s;" (sgen_ctyp ctyp) (sgen_name id)
        | Init_static vl -> ksprintf string "  static %s %s = %s;" (sgen_ctyp ctyp) (sgen_name id) (sgen_value ctyp vl)
        | Init_json_key parts ->
            let name = sgen_name id in
            (* Separate declaration and assignment avoids errors about goto's crossing the initialisation
               when compiling this code as C++. Unfortunately this also means we can't use an initialiser
               list to assign its value. We could move all of these to the top of the function but
               I don't know how to do that. *)
            ksprintf string "  const_sail_string %s[%d];" name (List.length parts)
            ^^ Util.fold_left_index
                 (fun i acc part -> acc ^^ hardline ^^ ksprintf string "  %s[%d] = \"%s\";" name i part)
                 empty parts
      )
    | I_reinit (ctyp, id, cval) ->
        codegen_instr fid ctx (ireset l ctyp id) ^^ hardline ^^ codegen_conversion l ctx (CL_id (id, ctyp)) cval
    | I_reset (ctyp, id) when is_stack_ctyp ctx ctyp ->
        string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_name id))
    | I_reset (ctyp, id) -> sail_recreate ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_return cval -> twice space ^^ c_return (string (sgen_cval cval))
    | I_throw _ -> c_error ~loc:l "I_throw reached code generator"
    | I_undefined ctyp ->
        let rec codegen_exn_return ctyp =
          match ctyp with
          | ctyp when is_c_repr_u320 ctyp -> ("u320_zero()", [])
          | ctyp when is_c_repr_u256 ctyp -> ("u256_zero()", [])
          | ctyp when is_c_repr_fixed_bytes ctyp -> (sprintf "%s_zero()" (sgen_ctyp_name ctyp), [])
          | CT_unit -> ("UNIT", [])
          | CT_fint width when width > 64 -> ("((__int128)INT64_C(0xdeadc0de))", [])
          | (CT_fint _ | CT_fuint _) as ctyp -> (sprintf "((%s)UINT64_C(0xdeadc0de))" (sgen_ctyp ctyp), [])
          | CT_lint when !optimize_fixed_int -> ("((sail_int) 0xdeadc0de)", [])
          | CT_fbits 1 -> ("UINT64_C(0)", [])
          | CT_fbits _ -> ("UINT64_C(0xdeadc0de)", [])
          | CT_sbits _ -> ("undefined_sbits()", [])
          | CT_lbits when !optimize_fixed_bits -> ("undefined_lbits(false)", [])
          | CT_bool -> ("false", [])
          | CT_enum _ -> (sprintf "((%s)0)" (sgen_ctyp ctyp), [])
          | ctyp when is_c_repr_u128 ctyp -> ("u128_zero()", [])
          | ctyp when is_c_repr_u320 ctyp -> ("u320_zero()", [])
          | ctyp when is_c_repr_u256 ctyp -> ("u256_zero()", [])
          | CT_tup ctyps when is_stack_ctyp ctx ctyp ->
              let gs = ngensym () in
              let fold (n, ctyp) (inits, prev) =
                let init, prev' = codegen_exn_return ctyp in
                (sprintf ".%s = %s" (sgen_tuple_id n) init :: inits, prev @ prev')
              in
              let inits, prev = List.fold_right fold (List.mapi (fun i x -> (i, x)) ctyps) ([], []) in
              ( sgen_name gs,
                [
                  sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name gs)
                  ^ Util.string_of_list ", " (fun x -> x) inits
                  ^ " };";
                ]
                @ prev
              )
          | CT_struct _ when is_stack_ctyp ctx ctyp ->
              let fields = struct_field_bindings l ctx ctyp |> snd |> Bindings.bindings in
              let gs = ngensym () in
              let fold (id, ctyp) (inits, prev) =
                let init, prev' = codegen_exn_return ctyp in
                (sprintf ".%s = %s" (sgen_id id) init :: inits, prev @ prev')
              in
              let inits, prev = List.fold_right fold fields ([], []) in
              ( sgen_name gs,
                [
                  sprintf "struct %s %s = { " (sgen_ctyp_name ctyp) (sgen_name gs)
                  ^ Util.string_of_list ", " (fun x -> x) inits
                  ^ " };";
                ]
                @ prev
              )
          | CT_variant _ when is_stack_ctyp ctx ctyp ->
              let gs = ngensym () in
              ( sgen_name gs,
                [sprintf "struct %s %s = {0};" (sgen_ctyp_name ctyp) (sgen_name gs)]
              )
          | CT_fvector _ when is_stack_ctyp ctx ctyp ->
              let gs = ngensym () in
              (sgen_name gs, [sprintf "%s %s = {0};" (sgen_ctyp ctyp) (sgen_name gs)])
          | CT_ref _ -> ("NULL", [])
          | ctyp -> c_error ("Cannot create undefined value for type: " ^ string_of_ctyp ctyp)
        in
        let ret, prev = codegen_exn_return ctyp in
        separate_map hardline (fun str -> string ("  " ^ str)) (List.rev prev)
        ^^ hardline
        ^^ string (Printf.sprintf "  return %s;" ret)
    | I_comment str -> string ("  /* " ^ str ^ " */")
    | I_label str -> string (str ^ ": ;")
    | I_goto str -> string (Printf.sprintf "  goto %s;" str)
    | I_raw _ when ctx.no_raw -> empty
    | I_raw str -> string ("  " ^ str)
    | I_end _ -> assert false
    | I_exit _ -> string ("  sail_match_failure(\"" ^ String.escaped (string_of_id fid) ^ "\");")

  let codegen_type_def ctx =
    let open Printf in
    function
    | CTD_abstract (id, ctyp, inst) ->
        let setter_prototype, setter =
          match inst with
          | CTDI_none ->
              ( ksprintf string "void sail_set_abstract_%s(%s v);" (string_of_id id) (sgen_ctyp ctyp),
                c_function ~return:"void"
                  (ksprintf string "%ssail_set_abstract_%s(%s v)" (class_impl_prefix ()) (string_of_id id)
                     (sgen_ctyp ctyp)
                  )
                  [
                    ( if is_stack_ctyp ctx ctyp then
                        ksprintf c_stmt "%s = v" (NameGen.to_string ~prefix:"abstract_" () id)
                      else
                        sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&%s, v"
                          (NameGen.to_string ~prefix:"abstract_" () id)
                    );
                  ]
              )
          | CTDI_instrs init ->
              ( ksprintf string "void sail_set_abstract_%s(void);" (string_of_id id),
                c_function ~return:"void"
                  (ksprintf string "%ssail_set_abstract_%s(void)" (class_impl_prefix ()) (string_of_id id))
                  [separate_map hardline (codegen_instr (mk_id "set_abstract") ctx) init]
              )
        in
        [
          FunctionDeclaration setter_prototype;
          FunctionDefinition setter;
          VariableDefinition
            (ksprintf string "%s %s%s;" (sgen_ctyp ctyp)
               (NameGen.to_string ~prefix:"abstract_" () id)
               (variable_zero_init ())
            );
        ]
    | CTD_enum (id, (first_id :: _ as ids)) ->
        let enum_name = sgen_id id in
        let enum_eq =
          c_function ~return:"static bool"
            (sail_equal enum_name "enum %s op1, enum %s op2" enum_name enum_name)
            [c_stmt "return op1 == op2"]
        in
        let enum_undefined =
          let name = sgen_id id in
          string (Printf.sprintf "static enum %s UNDEFINED(%s)(unit u) { return %s; }" name name (sgen_id first_id))
        in
        (* Conservatively use the smallest size of int to guard specifying storage size.  This assumes C++11,
           but could also be done for C23. *)
        let enum_type =
          if Config.cpp && List.length ids < 65536 then space ^^ colon ^^ space ^^ string "int" else empty
        in
        [
          TypeDeclaration
            (string (Printf.sprintf "// enum %s" (string_of_id id))
            ^^ hardline
            ^^ separate space
                 [
                   string "enum";
                   codegen_id id ^^ enum_type;
                   lbrace;
                   separate_map (comma ^^ space) codegen_id ids;
                   rbrace ^^ semi;
                 ]
            );
          StaticFunctionDefinition enum_eq;
          StaticFunctionDefinition enum_undefined;
        ]
    | CTD_enum (id, []) -> c_error ("Cannot compile empty enum " ^ string_of_id id)
    | CTD_abbrev (_, ctyp) when Config.optimized_model && not (is_stack_ctyp ctx ctyp) ->
        (* Transparent source aliases do not allocate storage themselves.  Do
           not leak an otherwise-unused generic alias such as [sail_int] into
           the fixed optimized ABI; any concrete use of it is diagnosed by
           the representation validator before code generation. *)
        []
    | CTD_abbrev (id, ctyp) ->
        [
          TypeDeclaration
            (ksprintf string "// type abbreviation %s" (string_of_id id)
            ^^ hardline
            ^^ separate space [string "typedef"; string (sgen_ctyp ctyp); codegen_id id]
            ^^ semi
            );
        ]
    | CTD_struct (id, _, ctors) ->
        let struct_name = sgen_id id in
        let struct_ctyp = CT_struct (id, []) in
        (* Generate a set_T function for every struct T *)
        let set_field (id, ctyp) =
          if is_stack_ctyp ctx ctyp then ksprintf c_stmt "rop->%s = op.%s" (sgen_id id) (sgen_id id)
          else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->%s, op.%s" (sgen_id id) (sgen_id id)
        in
        let struct_copy =
          c_function ~return:"static void"
            (sail_copy struct_name "struct %s *rop, const struct %s op" struct_name struct_name)
            (List.map set_field ctors)
        in
        (* Derive the various lifecycle functions create/recreate/kill for the struct *)
        let derive (f : string -> ('a, unit, string, document) format4 -> 'a) =
          let per_field (field_id, ctyp) =
            if not (is_stack_ctyp ctx ctyp) then [f (sgen_ctyp_name ctyp) "&op->%s" (sgen_id field_id) ^^ semi] else []
          in
          c_function ~return:"static void"
            (f struct_name "struct %s *op" struct_name)
            (List.concat (List.map per_field ctors))
        in
        let struct_eq =
          let field_eq (field_id, ctyp) =
            let field = sgen_id field_id in
            codegen_equal ctyp (sprintf "op1.%s" field) (sprintf "op2.%s" field)
          in
          c_function ~return:"static bool"
            (sail_equal (sgen_id id) "struct %s op1, struct %s op2" (sgen_id id) (sgen_id id))
            [string "return" ^^ space ^^ separate_map (string " && ") field_eq ctors ^^ semi]
        in
        (* Generate the struct and add the generated functions *)
        let struct_field (id, ctyp) = string (sgen_ctyp ctyp) ^^ space ^^ codegen_id id in

        [
          TypeDeclaration
            (string (Printf.sprintf "// struct %s" (string_of_id id))
            ^^ hardline ^^ string "struct" ^^ space ^^ codegen_id id ^^ space
            ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) struct_field ctors ^^ semi) rbrace
            ^^ semi
            );
        ]
        @
        ( if Config.optimized_model && is_stack_ctyp ctx struct_ctyp then []
          else [StaticFunctionDefinition struct_copy]
        )
        @ ( if (not Config.optimized_model) || not (is_stack_ctyp ctx struct_ctyp) then
              [
                StaticFunctionDefinition (derive sail_create);
                StaticFunctionDefinition (derive sail_recreate);
                StaticFunctionDefinition (derive sail_kill);
              ]
            else []
          )
        @ [StaticFunctionDefinition struct_eq]
    | CTD_variant (id, _, tus) ->
        let variant_ctyp = CT_variant (id, []) in
        let stack_variant = is_stack_ctyp ctx variant_ctyp in
        let codegen_tu (ctor_id, ctyp) =
          separate space [string "struct"; lbrace; string (sgen_ctyp ctyp); codegen_id ctor_id ^^ semi; rbrace]
        in
        (* Create a switch that does something for each constructor *)
        let each_ctor v f ctors =
          let cases, default =
            List.fold_left
              (fun (cases, default) (ctor_id, ctyp) ->
                match f ctor_id ctyp with
                | Some op -> ((ksprintf string "Kind_%s" (sgen_id ctor_id), [op]) :: cases, default)
                | None -> (cases, true)
              )
              ([], false) ctors
          in
          (* Avoid outputting empty switches. This is here instead of in `c_switch` because
            in `c_switch` we don't know that the condition expression has no side effects. *)
          if cases = [] then empty else c_switch ~default (ksprintf string "(%skind)" v) (List.rev cases)
        in
        let codegen_init =
          let n = sgen_id id in
          let ctor_id, ctyp = List.hd tus in
          c_function ~return:"static void" (sail_create n "struct %s *op" n)
            ([string (Printf.sprintf "op->kind = Kind_%s;" (sgen_id ctor_id))]
            @
            if not (is_stack_ctyp ctx ctyp) then
              [sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&op->variants.%s" (sgen_id ctor_id)]
            else []
            )
        in
        let codegen_reinit =
          let n = sgen_id id in
          c_function ~return:"static void" (sail_recreate n "struct %s *op" n) []
        in
        let clear_field v ctor_id ctyp =
          if is_stack_ctyp ctx ctyp then None
          else Some (sail_kill ~suffix:";" (sgen_ctyp_name ctyp) "&%s->variants.%s" v (sgen_id ctor_id))
        in
        let codegen_clear =
          let n = sgen_id id in
          c_function ~return:"static void" (sail_kill n "struct %s *op" n) [each_ctor "op->" (clear_field "op") tus]
        in
        let codegen_ctor (ctor_id, ctyp) =
          let ctor_args = Printf.sprintf "%s op" (sgen_const_ctyp ctyp) in
          if Config.optimized_model && stack_variant then
            let n = sgen_id id in
            c_function ~return:("static struct " ^ n)
              (ksprintf string "%s(%s%s)" (sgen_function_id ctor_id) (extra_params ()) ctor_args)
              [
                ksprintf string "struct %s result;" n;
                string ("result.kind = Kind_" ^ sgen_id ctor_id) ^^ semi;
                ksprintf string "result.variants.%s = op;" (sgen_id ctor_id);
                c_return (string "result");
              ]
          else
            c_function ~return:"static void"
              (ksprintf string "%s(%sstruct %s *rop, %s)" (sgen_function_id ctor_id) (extra_params ()) (sgen_id id)
                 ctor_args
              )
              ([each_ctor "rop->" (clear_field "rop") tus; string ("rop->kind = Kind_" ^ sgen_id ctor_id) ^^ semi]
              @
              if is_stack_ctyp ctx ctyp then [ksprintf string "rop->variants.%s = op;" (sgen_id ctor_id)]
              else
                [
                  sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&rop->variants.%s" (sgen_id ctor_id);
                  sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->variants.%s, op" (sgen_id ctor_id);
                ]
              )
        in
        let codegen_setter =
          let n = sgen_id id in
          let set_field ctor_id ctyp =
            Some
              ( if is_stack_ctyp ctx ctyp then
                  string (Printf.sprintf "rop->variants.%s = op.variants.%s;" (sgen_id ctor_id) (sgen_id ctor_id))
                else
                  sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&rop->variants.%s" (sgen_id ctor_id)
                  ^^ sail_copy ~prefix:" " ~suffix:";" (sgen_ctyp_name ctyp) "&rop->variants.%s, op.variants.%s"
                       (sgen_id ctor_id) (sgen_id ctor_id)
              )
          in
          c_function ~return:"static void"
            (sail_copy n "struct %s *rop, struct %s op" n n)
            [
              each_ctor "rop->" (clear_field "rop") tus ^^ semi;
              c_stmt "rop->kind = op.kind";
              each_ctor "op." set_field tus;
            ]
        in
        let codegen_eq =
          let codegen_eq_test ctor_id ctyp =
            c_return
              (codegen_equal ctyp
                 (sprintf "op1.variants.%s" (sgen_id ctor_id))
                 (sprintf "op2.variants.%s" (sgen_id ctor_id))
              )
          in
          let codegen_eq_tests ctors =
            c_if (ksprintf string "(op1.kind != op2.kind)") [c_return (string "false")]
            ^^ hardline
            ^^ c_switch (string "(op1.kind)")
                 (List.map
                    (fun (ctor_id, ctyp) ->
                      (ksprintf string "Kind_%s" (sgen_id ctor_id), [codegen_eq_test ctor_id ctyp])
                    )
                    ctors
                 )
            ^^ hardline
            (* This should be unreachable. *)
            ^^ c_return (string "false")
          in
          let n = sgen_id id in
          c_function ~return:"static bool" (sail_equal n "struct %s op1, struct %s op2" n n) [codegen_eq_tests tus]
        in
        [
          TypeDeclaration
            (string (Printf.sprintf "// union %s" (string_of_id id))
            ^^ hardline ^^ string "enum" ^^ space
            ^^ string ("kind_" ^ sgen_id id)
            ^^ space
            ^^ separate space
                 [
                   lbrace;
                   separate_map (comma ^^ space) (fun id -> string ("Kind_" ^ sgen_id id)) (List.map fst tus);
                   rbrace ^^ semi;
                 ]
            );
          TypeDeclaration
            (string "struct" ^^ space ^^ codegen_id id ^^ space
            ^^ surround 2 0 lbrace
                 (separate space [string "enum"; string ("kind_" ^ sgen_id id); string "kind" ^^ semi]
                 ^^ hardline ^^ string "union" ^^ space
                 ^^ surround 2 0 lbrace (separate_map (semi ^^ hardline) codegen_tu tus ^^ semi) rbrace
                 ^^ space ^^ string "variants" ^^ semi
                 )
                 rbrace
            ^^ semi
            );
        ]
        @ ( if Config.optimized_model && stack_variant then []
            else
              [
                StaticFunctionDefinition codegen_init;
                StaticFunctionDefinition codegen_reinit;
                StaticFunctionDefinition codegen_clear;
                StaticFunctionDefinition codegen_setter;
              ]
          )
        @ [StaticFunctionDefinition codegen_eq]
        @ List.map (fun tu -> StaticFunctionDefinition (codegen_ctor tu)) tus
        (* If this is the exception type, then we setup up some global variables to deal with exceptions. *)
        @
        if string_of_id id = "exception" && Config.optimized_model then
          [
            VariableDeclaration (ksprintf string "extern struct %s current_exception;" (sgen_id id));
            VariableDefinition (ksprintf string "struct %s current_exception = {0};" (sgen_id id));
            VariableDeclaration (string "extern bool have_exception;");
            VariableDefinition (string "bool have_exception = false;");
          ]
        else if string_of_id id = "exception" then
          [
            VariableDeclaration (ksprintf string "extern struct %s *current_exception;" (sgen_id id));
            VariableDefinition (ksprintf string "struct %s *current_exception = NULL;" (sgen_id id));
            VariableDeclaration (string "extern bool have_exception;");
            VariableDefinition (string "bool have_exception = false;");
            VariableDeclaration (string "extern sail_string *throw_location;");
            VariableDefinition (string "sail_string *throw_location = NULL;");
          ]
        else []

  (** GLOBAL: because C doesn't have real anonymous tuple types (anonymous structs don't quite work the way we need)
      every tuple type in the spec becomes some generated named struct in C. This is done in such a way that every
      possible tuple type has a unique name associated with it. This global variable keeps track of these generated
      struct names, so we never generate two copies of the struct that is used to represent them in C. The way this
      works is that codegen_def scans each definition's type annotations for tuple types and generates the required
      structs using codegen_type_def before the actual definition is generated by codegen_def'. This variable should be
      reset to empty only when the entire AST has been translated to C. **)
  let generated = ref IdSet.empty

  (* The specialized backend can lower every use of the generic integer and
     bitvector representations away while still generating native vector,
     fixed-byte, and u256 types.  Their compatibility helpers used to be
     emitted unconditionally, leaving dead sail_int/lbits code in otherwise
     runtime-free output.  These flags are computed from the final optimized
     JIB immediately before code generation. *)
  let emit_generic_sail_int_helpers = ref true
  let emit_generic_lbits_helpers = ref true

  let native_int_conversion_failure_id = mk_id "__sail_native_int_conversion_failure"

  let codegen_native_int_conversion_failure () =
    if IdSet.mem native_int_conversion_failure_id !generated then []
    else (
      generated := IdSet.add native_int_conversion_failure_id !generated;
      [
        StaticFunctionDefinition
          (string
             {|
static inline void sail_native_conversion_failure(const char *operation) {
  fprintf(stderr, "Sail C backend: %s\n", operation);
  exit(EXIT_FAILURE);
}
|}
          );
      ]
    )

  let codegen_u128 () =
    if IdSet.mem c_repr_u128_id !generated then []
    else (
      generated := IdSet.add c_repr_u128_id !generated;
      let typedef =
        string
          {|
#ifndef SAIL_U128_DEFINED
#define SAIL_U128_DEFINED
typedef struct { uint64_t limbs[2]; } sail_u128;
#endif
|}
      in
      let helpers =
        string
          {|

static inline sail_u128 u128_zero(void) {
  sail_u128 result = {{0}};
  return result;
}

static inline sail_u128 u128_of_u64(const uint64_t value) {
  sail_u128 result = {{value, UINT64_C(0)}};
  return result;
}

static inline uint64_t u128_to_u64(const sail_u128 value) {
  if (value.limbs[1] != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint64_t domain");
  }
  return value.limbs[0];
}

static inline uint64_t u128_extract_u64(const sail_u128 value, const uint64_t start) {
  if (start >= UINT64_C(128)) return UINT64_C(0);
  const size_t limb = (size_t)(start >> 6);
  const unsigned offset = (unsigned)(start & UINT64_C(63));
  uint64_t result = value.limbs[limb] >> offset;
  if (offset != 0 && limb + 1 < 2) result |= value.limbs[limb + 1] << (64 - offset);
  return result;
}

static inline bool eq_u128(const sail_u128 lhs, const sail_u128 rhs) {
  return lhs.limbs[0] == rhs.limbs[0] && lhs.limbs[1] == rhs.limbs[1];
}

static inline bool u128_eq_u64(const sail_u128 lhs, const uint64_t rhs) {
  return lhs.limbs[0] == rhs && lhs.limbs[1] == UINT64_C(0);
}

static inline sail_u128 u128_not(const sail_u128 value) {
  sail_u128 result = {{~value.limbs[0], ~value.limbs[1]}};
  return result;
}

static inline sail_u128 u128_and(const sail_u128 lhs, const sail_u128 rhs) {
  sail_u128 result = {{lhs.limbs[0] & rhs.limbs[0], lhs.limbs[1] & rhs.limbs[1]}};
  return result;
}

static inline sail_u128 u128_or(const sail_u128 lhs, const sail_u128 rhs) {
  sail_u128 result = {{lhs.limbs[0] | rhs.limbs[0], lhs.limbs[1] | rhs.limbs[1]}};
  return result;
}

static inline sail_u128 u128_xor(const sail_u128 lhs, const sail_u128 rhs) {
  sail_u128 result = {{lhs.limbs[0] ^ rhs.limbs[0], lhs.limbs[1] ^ rhs.limbs[1]}};
  return result;
}

static inline bool u128_lt(const sail_u128 lhs, const sail_u128 rhs) {
  return lhs.limbs[1] != rhs.limbs[1]
      ? lhs.limbs[1] < rhs.limbs[1]
      : lhs.limbs[0] < rhs.limbs[0];
}

static inline bool u128_lt_u64(const sail_u128 lhs, const uint64_t rhs) {
  return lhs.limbs[1] == UINT64_C(0) && lhs.limbs[0] < rhs;
}

static inline bool u64_lt_u128(const uint64_t lhs, const sail_u128 rhs) {
  return rhs.limbs[1] != UINT64_C(0) || lhs < rhs.limbs[0];
}

static inline sail_u128 u128_add(const sail_u128 lhs, const sail_u128 rhs) {
  sail_u128 result;
  result.limbs[0] = lhs.limbs[0] + rhs.limbs[0];
  result.limbs[1] = lhs.limbs[1] + rhs.limbs[1]
                  + (result.limbs[0] < lhs.limbs[0]);
  return result;
}

static inline sail_u128 u128_add_u64(const sail_u128 lhs, const uint64_t rhs) {
  sail_u128 result = lhs;
  result.limbs[0] += rhs;
  result.limbs[1] += result.limbs[0] < lhs.limbs[0];
  return result;
}

static inline sail_u128 u128_add_u64_u64(const uint64_t lhs,
                                         const uint64_t rhs) {
  sail_u128 result = {{lhs + rhs, lhs + rhs < lhs}};
  return result;
}

static inline sail_u128 u128_sub(const sail_u128 lhs, const sail_u128 rhs) {
  sail_u128 result;
  result.limbs[0] = lhs.limbs[0] - rhs.limbs[0];
  result.limbs[1] = lhs.limbs[1] - rhs.limbs[1]
                  - (lhs.limbs[0] < rhs.limbs[0]);
  return result;
}

static inline sail_u128 u128_sub_u64(const sail_u128 lhs, const uint64_t rhs) {
  sail_u128 result = lhs;
  result.limbs[0] -= rhs;
  result.limbs[1] -= lhs.limbs[0] < rhs;
  return result;
}

static inline uint64_t u64_sub_u128(const uint64_t lhs, const sail_u128 rhs) {
  return lhs - rhs.limbs[0];
}

static inline sail_u128 u128_sub_u64_u64(const uint64_t lhs,
                                         const uint64_t rhs) {
  sail_u128 result = {{lhs - rhs, UINT64_C(0)}};
  return result;
}

static inline sail_u128 u128_mul(const sail_u128 lhs, const sail_u128 rhs) {
  const unsigned __int128 low = (unsigned __int128)lhs.limbs[0] * rhs.limbs[0];
  sail_u128 result;
  result.limbs[0] = (uint64_t)low;
  result.limbs[1] = (uint64_t)(low >> 64)
                  + lhs.limbs[0] * rhs.limbs[1]
                  + lhs.limbs[1] * rhs.limbs[0];
  return result;
}

static inline sail_u128 u128_mul_u64(const sail_u128 lhs, const uint64_t rhs) {
  const unsigned __int128 low = (unsigned __int128)lhs.limbs[0] * rhs;
  sail_u128 result;
  result.limbs[0] = (uint64_t)low;
  result.limbs[1] = (uint64_t)(low >> 64) + lhs.limbs[1] * rhs;
  return result;
}

static inline sail_u128 u128_mul_u64_u64(const uint64_t lhs,
                                         const uint64_t rhs) {
  const unsigned __int128 product = (unsigned __int128)lhs * rhs;
  sail_u128 result = {{(uint64_t)product, (uint64_t)(product >> 64)}};
  return result;
}

static inline bool u128_is_zero(const sail_u128 value) {
  return (value.limbs[0] | value.limbs[1]) == UINT64_C(0);
}

/* Integer division helpers are emitted only for JIB operations carrying the
 * nonzero-divisor proof marker.  Do not re-check that source invariant here:
 * an unproved division remains in Sail's mathematical integer runtime. */
static inline void u128_divrem_u64(const sail_u128 dividend,
                                   const uint64_t divisor,
  sail_u128 *quotient,
                                   uint64_t *remainder) {
  sail_u128 q = {{0}};
  uint64_t r = UINT64_C(0);
  q.limbs[1] = dividend.limbs[1] / divisor;
  r = dividend.limbs[1] % divisor;
  const unsigned __int128 partial =
      ((unsigned __int128)r << 64) | dividend.limbs[0];
  q.limbs[0] = (uint64_t)(partial / divisor);
  r = (uint64_t)(partial % divisor);
  if (quotient != NULL) *quotient = q;
  if (remainder != NULL) *remainder = r;
}

/* Two-limb specialization of normalized Knuth division.  Like ruint, it
 * dispatches the one-limb divisor case separately and computes at most one
 * quotient limb for a normalized two-limb divisor. */
static inline void u128_divrem(const sail_u128 dividend,
                               const sail_u128 divisor,
                               sail_u128 *quotient,
  sail_u128 *remainder) {
  sail_u128 q = {{0}};
  sail_u128 r = {{0}};
  if (divisor.limbs[1] == UINT64_C(0)) {
    uint64_t rem = UINT64_C(0);
    u128_divrem_u64(dividend, divisor.limbs[0], &q, &rem);
    r.limbs[0] = rem;
    goto done;
  }

  if (u128_lt(dividend, divisor)) {
    r = dividend;
    goto done;
  }

  const unsigned shift = (unsigned)__builtin_clzll(divisor.limbs[1]);
  uint64_t v0;
  uint64_t v1;
  uint64_t u0;
  uint64_t u1;
  uint64_t u2;
  if (shift == 0) {
    v0 = divisor.limbs[0];
    v1 = divisor.limbs[1];
    u0 = dividend.limbs[0];
    u1 = dividend.limbs[1];
    u2 = UINT64_C(0);
  } else {
    v0 = divisor.limbs[0] << shift;
    v1 = (divisor.limbs[1] << shift)
       | (divisor.limbs[0] >> (64 - shift));
    u0 = dividend.limbs[0] << shift;
    u1 = (dividend.limbs[1] << shift)
       | (dividend.limbs[0] >> (64 - shift));
    u2 = dividend.limbs[1] >> (64 - shift);
  }

  uint64_t qhat;
  uint64_t rhat;
  bool rhat_overflow = false;
  if (u2 == v1) {
    qhat = UINT64_MAX;
    rhat = u1 + v1;
    rhat_overflow = rhat < u1;
  } else {
    const unsigned __int128 top = ((unsigned __int128)u2 << 64) | u1;
    qhat = (uint64_t)(top / v1);
    rhat = (uint64_t)(top % v1);
  }
  while (!rhat_overflow
         && (unsigned __int128)qhat * v0
                > (((unsigned __int128)rhat << 64) | u0)) {
    qhat--;
    const uint64_t next = rhat + v1;
    rhat_overflow = next < rhat;
    rhat = next;
  }

  const unsigned __int128 p0 = (unsigned __int128)qhat * v0;
  const uint64_t p0_low = (uint64_t)p0;
  const uint64_t p0_high = (uint64_t)(p0 >> 64);
  const uint64_t borrow0 = u0 < p0_low;
  u0 -= p0_low;

  const unsigned __int128 p1 = (unsigned __int128)qhat * v1
                              + p0_high + borrow0;
  const uint64_t p1_low = (uint64_t)p1;
  const uint64_t p1_high = (uint64_t)(p1 >> 64);
  const uint64_t borrow1 = u1 < p1_low;
  u1 -= p1_low;
  const uint64_t top_subtrahend = p1_high + borrow1;
  const bool top_overflow = top_subtrahend < p1_high;
  const bool negative = top_overflow || u2 < top_subtrahend;
  u2 -= top_subtrahend;

  if (negative) {
    qhat--;
    const uint64_t previous = u0;
    u0 += v0;
    const uint64_t carry = u0 < previous;
    u1 += v1 + carry;
  }
  q.limbs[0] = qhat;
  if (shift == 0) {
    r.limbs[0] = u0;
    r.limbs[1] = u1;
  } else {
    r.limbs[0] = (u0 >> shift) | (u1 << (64 - shift));
    r.limbs[1] = u1 >> shift;
  }

done:
  if (quotient != NULL) *quotient = q;
  if (remainder != NULL) *remainder = r;
}

static inline sail_u128 u128_div(const sail_u128 lhs, const sail_u128 rhs) {
  sail_u128 result;
  u128_divrem(lhs, rhs, &result, NULL);
  return result;
}

static inline sail_u128 u128_mod(const sail_u128 lhs, const sail_u128 rhs) {
  sail_u128 result;
  u128_divrem(lhs, rhs, NULL, &result);
  return result;
}

static inline sail_u128 u128_div_u64(const sail_u128 lhs, const uint64_t rhs) {
  sail_u128 result;
  u128_divrem_u64(lhs, rhs, &result, NULL);
  return result;
}

static inline sail_u128 u128_mod_u64(const sail_u128 lhs, const uint64_t rhs) {
  uint64_t remainder;
  u128_divrem_u64(lhs, rhs, NULL, &remainder);
  return u128_of_u64(remainder);
}
|}
      in
      let generic_sail_int_helpers =
        string
          {|
static inline sail_u128 u128_of_sail_int(const sail_int value) {
  sail_u128 result = {{0}};
  sail_int_to_u64_array(result.limbs, 2, value);
  return result;
}
|}
      in
      let helpers = helpers ^^ if !emit_generic_sail_int_helpers then generic_sail_int_helpers else empty in
      [TypeDeclaration typedef; StaticFunctionDefinition helpers]
    )

  let codegen_u256 () =
    if IdSet.mem c_repr_u256_id !generated then []
    else (
      generated := IdSet.add c_repr_u256_id !generated;
      let typedef =
        string
          {|
#ifndef SAIL_U128_DEFINED
#define SAIL_U128_DEFINED
typedef struct { uint64_t limbs[2]; } sail_u128;
#endif

#ifndef SAIL_U256_DEFINED
#define SAIL_U256_DEFINED
typedef struct { uint64_t limbs[4]; } sail_u256;
#endif
|}
      in
      let base_helpers =
        string
          {|
static inline sail_u256 u256_zero(void) {
  sail_u256 result = {{0}};
  return result;
}

static inline sail_u256 u256_of_u128(const sail_u128 value) {
  sail_u256 result = {{value.limbs[0], value.limbs[1], UINT64_C(0), UINT64_C(0)}};
  return result;
}

static inline sail_u128 u128_of_u256(const sail_u256 value) {
  if (value.limbs[2] != UINT64_C(0) || value.limbs[3] != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint128_t domain");
  }
  sail_u128 result = {{value.limbs[0], value.limbs[1]}};
  return result;
}

static inline uint64_t u256_to_u64(const sail_u256 value) {
  if (value.limbs[1] != UINT64_C(0)
      || value.limbs[2] != UINT64_C(0)
      || value.limbs[3] != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint64_t domain");
  }
  return value.limbs[0];
}

static inline bool eq_u256(const sail_u256 lhs, const sail_u256 rhs) {
  return lhs.limbs[0] == rhs.limbs[0]
      && lhs.limbs[1] == rhs.limbs[1]
      && lhs.limbs[2] == rhs.limbs[2]
      && lhs.limbs[3] == rhs.limbs[3];
}

static inline uint64_t u256_bit(const sail_u256 value, const int64_t index) {
  if (index < 0 || index >= 256) return UINT64_C(0);
  return (value.limbs[(uint64_t)index >> 6] >> ((uint64_t)index & UINT64_C(63))) & UINT64_C(1);
}

static inline uint64_t u256_extract_u64(const sail_u256 value, const uint64_t start) {
  if (start >= UINT64_C(256)) return UINT64_C(0);
  const size_t limb = (size_t)(start >> 6);
  const unsigned offset = (unsigned)(start & UINT64_C(63));
  uint64_t result = value.limbs[limb] >> offset;
  if (offset != 0 && limb + 1 < 4) result |= value.limbs[limb + 1] << (64 - offset);
  return result;
}

static inline sail_u256 u256_update_u64(sail_u256 value, const uint64_t index,
                                        const uint64_t bit) {
  if (index >= UINT64_C(256)) return value;
  const size_t limb = (size_t)(index >> 6);
  const uint64_t mask = UINT64_C(1) << (index & UINT64_C(63));
  if ((bit & UINT64_C(1)) != 0) value.limbs[limb] |= mask;
  else value.limbs[limb] &= ~mask;
  return value;
}

static inline sail_u256 u256_update_i64(sail_u256 value, const int64_t index,
                                        const uint64_t bit) {
  if (index < INT64_C(0)) return value;
  return u256_update_u64(value, (uint64_t)index, bit);
}

static inline uint64_t fast_vector_access_u256(const sail_u256 value, const int64_t index) {
  return u256_bit(value, index);
}

static inline sail_u256 u256_not(const sail_u256 value) {
  sail_u256 result;
  for (size_t i = 0; i < 4; ++i) result.limbs[i] = ~value.limbs[i];
  return result;
}

static inline sail_u256 u256_and(const sail_u256 lhs, const sail_u256 rhs) {
  sail_u256 result;
  for (size_t i = 0; i < 4; ++i) result.limbs[i] = lhs.limbs[i] & rhs.limbs[i];
  return result;
}

static inline sail_u256 u256_or(const sail_u256 lhs, const sail_u256 rhs) {
  sail_u256 result;
  for (size_t i = 0; i < 4; ++i) result.limbs[i] = lhs.limbs[i] | rhs.limbs[i];
  return result;
}

static inline sail_u256 u256_xor(const sail_u256 lhs, const sail_u256 rhs) {
  sail_u256 result;
  for (size_t i = 0; i < 4; ++i) result.limbs[i] = lhs.limbs[i] ^ rhs.limbs[i];
  return result;
}

static inline sail_u256 u256_add(const sail_u256 lhs, const sail_u256 rhs) {
  sail_u256 result;
  uint64_t carry = UINT64_C(0);
  for (size_t i = 0; i < 4; ++i) {
    const uint64_t partial = lhs.limbs[i] + rhs.limbs[i];
    const uint64_t carry1 = partial < lhs.limbs[i];
    result.limbs[i] = partial + carry;
    const uint64_t carry2 = result.limbs[i] < partial;
    carry = carry1 | carry2;
  }
  return result;
}

static inline sail_u256 u256_add_u128_u128(const sail_u128 lhs,
                                           const sail_u128 rhs) {
  sail_u256 result = {{0}};
  const unsigned __int128 low =
      (unsigned __int128)lhs.limbs[0] + rhs.limbs[0];
  result.limbs[0] = (uint64_t)low;
  const unsigned __int128 high =
      (unsigned __int128)lhs.limbs[1] + rhs.limbs[1] + (low >> 64);
  result.limbs[1] = (uint64_t)high;
  result.limbs[2] = (uint64_t)(high >> 64);
  return result;
}

static inline sail_u256 u256_add_u128_u64(const sail_u128 lhs,
                                          const uint64_t rhs) {
  sail_u256 result = {{0}};
  const unsigned __int128 low = (unsigned __int128)lhs.limbs[0] + rhs;
  result.limbs[0] = (uint64_t)low;
  const unsigned __int128 high = (unsigned __int128)lhs.limbs[1] + (low >> 64);
  result.limbs[1] = (uint64_t)high;
  result.limbs[2] = (uint64_t)(high >> 64);
  return result;
}

static inline sail_u256 u256_add_u64_u128(const uint64_t lhs,
                                          const sail_u128 rhs) {
  return u256_add_u128_u64(rhs, lhs);
}

static inline sail_u256 u256_sub(const sail_u256 lhs, const sail_u256 rhs) {
  sail_u256 result;
  uint64_t borrow = UINT64_C(0);
  for (size_t i = 0; i < 4; ++i) {
    const uint64_t partial = lhs.limbs[i] - rhs.limbs[i];
    const uint64_t borrow1 = lhs.limbs[i] < rhs.limbs[i];
    result.limbs[i] = partial - borrow;
    const uint64_t borrow2 = partial < borrow;
    borrow = borrow1 | borrow2;
  }
  return result;
}

static inline sail_u256 u256_mul(const sail_u256 lhs, const sail_u256 rhs) {
  sail_u256 result = {{0}};
  for (size_t i = 0; i < 4; ++i) {
    unsigned __int128 carry = 0;
    for (size_t j = 0; i + j < 4; ++j) {
      const size_t k = i + j;
      const unsigned __int128 product = (unsigned __int128)lhs.limbs[i] * rhs.limbs[j];
      const unsigned __int128 sum = product + result.limbs[k] + carry;
      result.limbs[k] = (uint64_t)sum;
      carry = sum >> 64;
    }
  }
  return result;
}

static inline sail_u256 u256_mul_u128_u128(const sail_u128 lhs,
                                           const sail_u128 rhs) {
  sail_u256 result = {{0}};
  for (size_t i = 0; i < 2; ++i) {
    unsigned __int128 carry = 0;
    for (size_t j = 0; j < 2; ++j) {
      const size_t k = i + j;
      const unsigned __int128 sum =
          (unsigned __int128)lhs.limbs[i] * rhs.limbs[j]
          + result.limbs[k] + carry;
      result.limbs[k] = (uint64_t)sum;
      carry = sum >> 64;
    }
    result.limbs[i + 2] = (uint64_t)carry;
  }
  return result;
}

static inline sail_u256 u256_mul_u128_u64(const sail_u128 lhs,
                                          const uint64_t rhs) {
  sail_u256 result = {{0}};
  unsigned __int128 carry = 0;
  for (size_t i = 0; i < 2; ++i) {
    const unsigned __int128 product =
        (unsigned __int128)lhs.limbs[i] * rhs + carry;
    result.limbs[i] = (uint64_t)product;
    carry = product >> 64;
  }
  result.limbs[2] = (uint64_t)carry;
  return result;
}

static inline sail_u256 u256_mul_u64_u128(const uint64_t lhs,
                                          const sail_u128 rhs) {
  return u256_mul_u128_u64(rhs, lhs);
}

static inline bool u256_is_zero(const sail_u256 value) {
  return (value.limbs[0] | value.limbs[1] | value.limbs[2] | value.limbs[3])
      == UINT64_C(0);
}

static inline bool u256_lt(const sail_u256 lhs, const sail_u256 rhs) {
  for (size_t i = 4; i-- > 0;) {
    if (lhs.limbs[i] != rhs.limbs[i]) return lhs.limbs[i] < rhs.limbs[i];
  }
  return false;
}

static inline bool u256_eq_u128(const sail_u256 lhs, const sail_u128 rhs) {
  return lhs.limbs[0] == rhs.limbs[0]
      && lhs.limbs[1] == rhs.limbs[1]
      && lhs.limbs[2] == UINT64_C(0)
      && lhs.limbs[3] == UINT64_C(0);
}

static inline bool u256_lt_u128(const sail_u256 lhs, const sail_u128 rhs) {
  if ((lhs.limbs[2] | lhs.limbs[3]) != UINT64_C(0)) return false;
  if (lhs.limbs[1] != rhs.limbs[1]) return lhs.limbs[1] < rhs.limbs[1];
  return lhs.limbs[0] < rhs.limbs[0];
}

static inline bool u128_lt_u256(const sail_u128 lhs, const sail_u256 rhs) {
  if ((rhs.limbs[2] | rhs.limbs[3]) != UINT64_C(0)) return true;
  if (lhs.limbs[1] != rhs.limbs[1]) return lhs.limbs[1] < rhs.limbs[1];
  return lhs.limbs[0] < rhs.limbs[0];
}

static inline bool u256_eq_u64(const sail_u256 lhs, const uint64_t rhs) {
  return lhs.limbs[0] == rhs
      && lhs.limbs[1] == UINT64_C(0)
      && lhs.limbs[2] == UINT64_C(0)
      && lhs.limbs[3] == UINT64_C(0);
}

static inline bool u256_lt_u64(const sail_u256 lhs, const uint64_t rhs) {
  return lhs.limbs[1] == UINT64_C(0)
      && lhs.limbs[2] == UINT64_C(0)
      && lhs.limbs[3] == UINT64_C(0)
      && lhs.limbs[0] < rhs;
}

static inline bool u64_lt_u256(const uint64_t lhs, const sail_u256 rhs) {
  return rhs.limbs[1] != UINT64_C(0)
      || rhs.limbs[2] != UINT64_C(0)
      || rhs.limbs[3] != UINT64_C(0)
      || lhs < rhs.limbs[0];
}

static inline sail_u256 u256_add_u64(const sail_u256 lhs,
                                     const uint64_t rhs) {
  sail_u256 result = lhs;
  result.limbs[0] += rhs;
  uint64_t carry = result.limbs[0] < lhs.limbs[0];
  for (size_t i = 1; i < 4 && carry != UINT64_C(0); ++i) {
    const uint64_t previous = result.limbs[i];
    result.limbs[i]++;
    carry = result.limbs[i] < previous;
  }
  return result;
}

static inline sail_u256 u256_add_u128(const sail_u256 lhs,
                                      const sail_u128 rhs) {
  sail_u256 result = lhs;
  unsigned __int128 sum =
      (unsigned __int128)lhs.limbs[0] + rhs.limbs[0];
  result.limbs[0] = (uint64_t)sum;
  sum = (unsigned __int128)lhs.limbs[1] + rhs.limbs[1] + (sum >> 64);
  result.limbs[1] = (uint64_t)sum;
  uint64_t carry = (uint64_t)(sum >> 64);
  for (size_t i = 2; i < 4 && carry != UINT64_C(0); ++i) {
    const uint64_t previous = result.limbs[i];
    result.limbs[i]++;
    carry = result.limbs[i] < previous;
  }
  return result;
}

static inline sail_u256 u256_sub_u64(const sail_u256 lhs,
                                     const uint64_t rhs) {
  sail_u256 result = lhs;
  result.limbs[0] -= rhs;
  uint64_t borrow = lhs.limbs[0] < rhs;
  for (size_t i = 1; i < 4 && borrow != UINT64_C(0); ++i) {
    const uint64_t previous = result.limbs[i];
    result.limbs[i]--;
    borrow = previous == UINT64_C(0);
  }
  return result;
}

static inline sail_u256 u256_sub_u128(const sail_u256 lhs,
                                      const sail_u128 rhs) {
  sail_u256 result = lhs;
  const uint64_t low = lhs.limbs[0] - rhs.limbs[0];
  uint64_t borrow = lhs.limbs[0] < rhs.limbs[0];
  const uint64_t high = lhs.limbs[1] - rhs.limbs[1];
  const uint64_t borrow1 = lhs.limbs[1] < rhs.limbs[1];
  result.limbs[0] = low;
  result.limbs[1] = high - borrow;
  const uint64_t borrow2 = high < borrow;
  borrow = borrow1 | borrow2;
  for (size_t i = 2; i < 4 && borrow != UINT64_C(0); ++i) {
    const uint64_t previous = result.limbs[i];
    result.limbs[i]--;
    borrow = previous == UINT64_C(0);
  }
  return result;
}

/* A valid natural subtraction with a u128 minuend proves that the u256
 * subtrahend's upper limbs are zero. */
static inline sail_u128 u128_sub_u256(const sail_u128 lhs,
                                      const sail_u256 rhs) {
  sail_u128 result;
  result.limbs[0] = lhs.limbs[0] - rhs.limbs[0];
  const uint64_t borrow = lhs.limbs[0] < rhs.limbs[0];
  result.limbs[1] = lhs.limbs[1] - rhs.limbs[1] - borrow;
  return result;
}

/* The Sail range checker proves that rhs fits and rhs <= lhs at each emitted
 * u64 - u256 call site.  The helper only expresses the selected C
 * representation; it does not add a second runtime semantics. */
static inline uint64_t u64_sub_u256(const uint64_t lhs,
                                    const sail_u256 rhs) {
  return lhs - rhs.limbs[0];
}

static inline sail_u256 u256_mul_u64(const sail_u256 lhs,
                                     const uint64_t rhs) {
  sail_u256 result = {{0}};
  unsigned __int128 carry = 0;
  for (size_t i = 0; i < 4; ++i) {
    const unsigned __int128 product =
        (unsigned __int128)lhs.limbs[i] * rhs + carry;
    result.limbs[i] = (uint64_t)product;
    carry = product >> 64;
  }
  return result;
}

static inline sail_u256 u256_mul_u128(const sail_u256 lhs,
                                      const sail_u128 rhs) {
  sail_u256 result = {{0}};
  for (size_t i = 0; i < 4; ++i) {
    unsigned __int128 carry = 0;
    for (size_t j = 0; j < 2 && i + j < 4; ++j) {
      const size_t k = i + j;
      const unsigned __int128 sum =
          (unsigned __int128)lhs.limbs[i] * rhs.limbs[j]
          + result.limbs[k] + carry;
      result.limbs[k] = (uint64_t)sum;
      carry = sum >> 64;
    }
    if (i + 2 < 4) result.limbs[i + 2] = (uint64_t)carry;
  }
  return result;
}

static inline sail_u256 u256_div_u64(const sail_u256 dividend,
                                     const uint64_t divisor) {
  sail_u256 quotient = {{0}};
  uint64_t remainder = UINT64_C(0);
  for (size_t i = 4; i-- > 0;) {
    const unsigned __int128 partial =
        ((unsigned __int128)remainder << 64) | dividend.limbs[i];
    quotient.limbs[i] = (uint64_t)(partial / divisor);
    remainder = (uint64_t)(partial % divisor);
  }
  return quotient;
}

static inline sail_u256 u256_mod_u64(const sail_u256 dividend,
                                     const uint64_t divisor) {
  sail_u256 result = {{0}};
  uint64_t remainder = UINT64_C(0);
  for (size_t i = 4; i-- > 0;) {
    const unsigned __int128 partial =
        ((unsigned __int128)remainder << 64) | dividend.limbs[i];
    remainder = (uint64_t)(partial % divisor);
  }
  result.limbs[0] = remainder;
  return result;
}

static inline size_t u256_significant_words(const uint64_t *value,
                                            size_t count) {
  while (count != 0 && value[count - 1] == UINT64_C(0)) count--;
  return count;
}

static inline unsigned u256_leading_zeros(const uint64_t value) {
  return value == UINT64_C(0) ? 64U : (unsigned)__builtin_clzll(value);
}

/* Knuth division, Algorithm D, in base 2^64.  The numerator has at most
 * eight limbs and the divisor at most four.  Callers either carry the JIB
 * nonzero proof or implement an explicit source-level zero-modulus branch. */
static inline void u256_divrem_words(const uint64_t *numerator,
                                     size_t numerator_count,
                                     const uint64_t divisor[4],
                                     uint64_t quotient[8],
                                     uint64_t remainder[4]) {
  uint64_t u[9] = {0};
  uint64_t v[4] = {0};
  const size_t un = u256_significant_words(numerator, numerator_count);
  const size_t vn = u256_significant_words(divisor, 4);

  if (quotient != NULL)
    for (size_t i = 0; i < 8; ++i) quotient[i] = UINT64_C(0);
  if (remainder != NULL)
    for (size_t i = 0; i < 4; ++i) remainder[i] = UINT64_C(0);
  if (un == 0) return;
  if (un < vn) {
    if (remainder != NULL)
      for (size_t i = 0; i < un; ++i) remainder[i] = numerator[i];
    return;
  }

  if (vn == 1) {
    uint64_t rem = UINT64_C(0);
    for (size_t i = un; i-- > 0;) {
      const unsigned __int128 partial =
          ((unsigned __int128)rem << 64) | numerator[i];
      if (quotient != NULL)
        quotient[i] = (uint64_t)(partial / divisor[0]);
      rem = (uint64_t)(partial % divisor[0]);
    }
    if (remainder != NULL) remainder[0] = rem;
    return;
  }

  const unsigned shift = u256_leading_zeros(divisor[vn - 1]);
  if (shift == 0) {
    for (size_t i = 0; i < vn; ++i) v[i] = divisor[i];
    for (size_t i = 0; i < un; ++i) u[i] = numerator[i];
  } else {
    uint64_t carry = UINT64_C(0);
    for (size_t i = 0; i < vn; ++i) {
      const uint64_t next = divisor[i] >> (64 - shift);
      v[i] = (divisor[i] << shift) | carry;
      carry = next;
    }
    carry = UINT64_C(0);
    for (size_t i = 0; i < un; ++i) {
      const uint64_t next = numerator[i] >> (64 - shift);
      u[i] = (numerator[i] << shift) | carry;
      carry = next;
    }
    u[un] = carry;
  }

  const size_t qn = un - vn + 1;
  for (size_t jj = qn; jj-- > 0;) {
    const size_t j = jj;
    uint64_t qhat;
    uint64_t rhat;
    bool rhat_overflow = false;
    if (u[j + vn] == v[vn - 1]) {
      qhat = UINT64_MAX;
      rhat = u[j + vn - 1] + v[vn - 1];
      rhat_overflow = rhat < u[j + vn - 1];
    } else {
      const unsigned __int128 top =
          ((unsigned __int128)u[j + vn] << 64) | u[j + vn - 1];
      qhat = (uint64_t)(top / v[vn - 1]);
      rhat = (uint64_t)(top % v[vn - 1]);
    }

    while (!rhat_overflow
           && (unsigned __int128)qhat * v[vn - 2]
                  > (((unsigned __int128)rhat << 64) | u[j + vn - 2])) {
      qhat--;
      const uint64_t next = rhat + v[vn - 1];
      rhat_overflow = next < rhat;
      rhat = next;
    }

    uint64_t borrow = UINT64_C(0);
    for (size_t i = 0; i < vn; ++i) {
      const unsigned __int128 product =
          (unsigned __int128)qhat * v[i] + borrow;
      const uint64_t low = (uint64_t)product;
      borrow = (uint64_t)(product >> 64) + (u[j + i] < low);
      u[j + i] -= low;
    }
    const bool negative = u[j + vn] < borrow;
    u[j + vn] -= borrow;

    if (negative) {
      qhat--;
      uint64_t carry = UINT64_C(0);
      for (size_t i = 0; i < vn; ++i) {
        const unsigned __int128 sum =
            (unsigned __int128)u[j + i] + v[i] + carry;
        u[j + i] = (uint64_t)sum;
        carry = (uint64_t)(sum >> 64);
      }
      u[j + vn] += carry;
    }
    if (quotient != NULL) quotient[j] = qhat;
  }

  if (remainder != NULL) {
    if (shift == 0) {
      for (size_t i = 0; i < vn; ++i) remainder[i] = u[i];
    } else {
      for (size_t i = 0; i < vn; ++i) {
        remainder[i] = u[i] >> shift;
        if (i + 1 < vn) remainder[i] |= u[i + 1] << (64 - shift);
      }
    }
  }
}

static inline sail_u256 u256_div_u128(const sail_u256 dividend,
                                      const sail_u128 divisor) {
  sail_u256 result = {{0}};
  const uint64_t words[4] = {
      divisor.limbs[0], divisor.limbs[1], UINT64_C(0), UINT64_C(0)};
  uint64_t quotient[8] = {0};
  u256_divrem_words(dividend.limbs, 4, words, quotient, NULL);
  for (size_t i = 0; i < 4; ++i) result.limbs[i] = quotient[i];
  return result;
}

static inline sail_u256 u256_mod_u128(const sail_u256 dividend,
                                      const sail_u128 divisor) {
  sail_u256 result = {{0}};
  const uint64_t words[4] = {
      divisor.limbs[0], divisor.limbs[1], UINT64_C(0), UINT64_C(0)};
  u256_divrem_words(dividend.limbs, 4, words, NULL, result.limbs);
  return result;
}

static inline sail_u128 u128_div_u256(const sail_u128 dividend,
                                      const sail_u256 divisor) {
  sail_u128 result = {{0}};
  if ((divisor.limbs[2] | divisor.limbs[3]) != UINT64_C(0)) return result;
  uint64_t quotient[8] = {0};
  u256_divrem_words(dividend.limbs, 2, divisor.limbs, quotient, NULL);
  result.limbs[0] = quotient[0];
  result.limbs[1] = quotient[1];
  return result;
}

static inline sail_u128 u128_mod_u256(const sail_u128 dividend,
                                      const sail_u256 divisor) {
  if ((divisor.limbs[2] | divisor.limbs[3]) != UINT64_C(0)) return dividend;
  uint64_t remainder[4] = {0};
  u256_divrem_words(dividend.limbs, 2, divisor.limbs, NULL, remainder);
  sail_u128 result = {{remainder[0], remainder[1]}};
  return result;
}

static inline sail_u256 u256_div(const sail_u256 dividend,
                                 const sail_u256 divisor) {
  sail_u256 result = {{0}};
  uint64_t quotient[8] = {0};
  u256_divrem_words(dividend.limbs, 4, divisor.limbs, quotient, NULL);
  for (size_t i = 0; i < 4; ++i) result.limbs[i] = quotient[i];
  return result;
}

static inline sail_u256 u256_mod(const sail_u256 dividend,
                                 const sail_u256 divisor) {
  sail_u256 result = {{0}};
  u256_divrem_words(dividend.limbs, 4, divisor.limbs, NULL, result.limbs);
  return result;
}

static inline sail_u256 u256_addmod(const sail_u256 lhs,
                                    const sail_u256 rhs,
                                    const sail_u256 modulus) {
  sail_u256 result = {{0}};
  uint64_t sum[5] = {0};
  uint64_t carry = UINT64_C(0);
  for (size_t i = 0; i < 4; ++i) {
    const unsigned __int128 wide =
        (unsigned __int128)lhs.limbs[i] + rhs.limbs[i] + carry;
    sum[i] = (uint64_t)wide;
    carry = (uint64_t)(wide >> 64);
  }
  sum[4] = carry;
  if (!u256_is_zero(modulus))
    u256_divrem_words(sum, 5, modulus.limbs, NULL, result.limbs);
  return result;
}

static inline sail_u256 u256_mulmod(const sail_u256 lhs,
                                    const sail_u256 rhs,
                                    const sail_u256 modulus) {
  sail_u256 result = {{0}};
  uint64_t product[8] = {0};
  for (size_t i = 0; i < 4; ++i) {
    uint64_t carry = UINT64_C(0);
    for (size_t j = 0; j < 4; ++j) {
      const size_t k = i + j;
      const unsigned __int128 wide =
          (unsigned __int128)lhs.limbs[i] * rhs.limbs[j]
          + product[k] + carry;
      product[k] = (uint64_t)wide;
      carry = (uint64_t)(wide >> 64);
    }
    product[i + 4] = carry;
  }
  if (!u256_is_zero(modulus))
    u256_divrem_words(product, 8, modulus.limbs, NULL, result.limbs);
  return result;
}

static inline sail_u256 u256_shiftl_u64(const sail_u256 value, const uint64_t amount) {
  sail_u256 result = {{0}};
  if (amount >= UINT64_C(256)) return result;
  const size_t words = (size_t)(amount >> 6);
  const unsigned bits = (unsigned)(amount & UINT64_C(63));
  for (size_t dst = 4; dst-- > words;) {
    result.limbs[dst] = value.limbs[dst - words] << bits;
    if (bits != 0 && dst > words) {
      result.limbs[dst] |= value.limbs[dst - words - 1] >> (64 - bits);
    }
  }
  return result;
}

static inline sail_u256 u256_shiftr_u64(const sail_u256 value, const uint64_t amount) {
  sail_u256 result = {{0}};
  if (amount >= UINT64_C(256)) return result;
  const size_t words = (size_t)(amount >> 6);
  const unsigned bits = (unsigned)(amount & UINT64_C(63));
  for (size_t dst = 0; dst + words < 4; ++dst) {
    result.limbs[dst] = value.limbs[dst + words] >> bits;
    if (bits != 0 && dst + words + 1 < 4) {
      result.limbs[dst] |= value.limbs[dst + words + 1] << (64 - bits);
    }
  }
  return result;
}

static inline sail_u256 u256_arith_shiftr_u64(const sail_u256 value, const uint64_t amount) {
  if ((value.limbs[3] >> 63) == 0) return u256_shiftr_u64(value, amount);
  return u256_not(u256_shiftr_u64(u256_not(value), amount));
}

static inline uint64_t u256_abs_i64(const int64_t amount) {
  return amount < 0 ? (uint64_t)(-(amount + 1)) + UINT64_C(1) : (uint64_t)amount;
}

static inline sail_u256 u256_shiftl_i64(const sail_u256 value, const int64_t amount) {
  return u256_shiftl_u64(value, u256_abs_i64(amount));
}

static inline sail_u256 u256_shiftr_i64(const sail_u256 value, const int64_t amount) {
  return u256_shiftr_u64(value, u256_abs_i64(amount));
}

static inline sail_u256 u256_arith_shiftr_i64(const sail_u256 value, const int64_t amount) {
  return u256_arith_shiftr_u64(value, u256_abs_i64(amount));
}

static inline sail_u256 u256_of_fbits(const uint64_t value) {
  sail_u256 result = {{0}};
  result.limbs[0] = value;
  return result;
}
|}
      in
      let string_helpers =
        string
          {|
static inline void string_of_u256(sail_string *result, const sail_u256 value) {
  sail_free(*result);
  const int bytes = asprintf(
      result,
      "0x%016" PRIx64 "%016" PRIx64 "%016" PRIx64 "%016" PRIx64,
      value.limbs[3], value.limbs[2], value.limbs[1], value.limbs[0]);
  if (bytes == -1) {
    fprintf(stderr, "Could not print a 256-bit value\n");
  }
}
|}
      in
      let generic_lbits_helpers =
        string
          {|
static inline sail_u256 u256_of_lbits(const lbits value) {
  sail_u256 result = {{0}};
  sail_lbits_to_u64_array(result.limbs, 4, value);
  return result;
}

static inline void lbits_of_u256(lbits *result, const sail_u256 value) {
  sail_lbits_from_u64_array(result, value.limbs, 4, UINT64_C(256));
}

static inline void decimal_string_of_u256(sail_string *result, const sail_u256 value) {
  lbits bits;
  CREATE(lbits)(&bits);
  lbits_of_u256(&bits, value);
  decimal_string_of_lbits(result, bits);
  KILL(lbits)(&bits);
}
|}
      in
      let generic_sail_int_helpers =
        string
          {|
static inline sail_u256 undefined_u256(const sail_int len) {
  (void)len;
  return u256_zero();
}

static inline uint64_t vector_access_u256(const sail_u256 value, const sail_int index) {
  return u256_bit(value, (int64_t)sail_int_get_ui(index));
}

static inline sail_u256 u256_shiftl(const sail_u256 value, const sail_int amount) {
  return u256_shiftl_u64(value, sail_int_get_ui(amount));
}

static inline sail_u256 u256_shiftr(const sail_u256 value, const sail_int amount) {
  return u256_shiftr_u64(value, sail_int_get_ui(amount));
}

static inline sail_u256 u256_arith_shiftr(const sail_u256 value, const sail_int amount) {
  return u256_arith_shiftr_u64(value, sail_int_get_ui(amount));
}

static inline void u256_unsigned(sail_int *result, const sail_u256 value) {
  sail_int_from_u64_array(result, value.limbs, 4);
}

static inline void u128_unsigned(sail_int *result, const sail_u128 value) {
  sail_int_from_u64_array(result, value.limbs, 2);
}

static inline void u256_signed(sail_int *result, const sail_u256 value) {
  sail_int_from_twos_complement_u64_array(result, value.limbs, 4);
}

static inline sail_u256 u256_of_sail_int(const sail_int value) {
  sail_u256 result = {{0}};
  sail_int_to_u64_array(result.limbs, 4, value);
  return result;
}
|}
      in
      let helpers =
        base_helpers
        ^^ (if Config.optimized_model then empty else string_helpers)
        ^^ (if !emit_generic_lbits_helpers then generic_lbits_helpers else empty)
        ^^ if !emit_generic_sail_int_helpers then generic_sail_int_helpers else empty
      in
      [TypeDeclaration typedef; StaticFunctionDefinition helpers]
    )

  let codegen_u320 () =
    if IdSet.mem c_repr_u320_id !generated then []
    else (
      generated := IdSet.add c_repr_u320_id !generated;
      let typedef =
        string
          {|
#ifndef SAIL_U128_DEFINED
#define SAIL_U128_DEFINED
typedef struct { uint64_t limbs[2]; } sail_u128;
#endif

#ifndef SAIL_U256_DEFINED
#define SAIL_U256_DEFINED
typedef struct { uint64_t limbs[4]; } sail_u256;
#endif

#ifndef SAIL_U320_DEFINED
#define SAIL_U320_DEFINED
typedef struct { uint64_t limbs[5]; } sail_u320;
#endif
|}
      in
      let base_helpers =
        string
          {|
static inline sail_u320 u320_zero(void) {
  sail_u320 result = {{0}};
  return result;
}

static inline sail_u320 u320_of_u64(const uint64_t value) {
  sail_u320 result = {{value, UINT64_C(0), UINT64_C(0), UINT64_C(0), UINT64_C(0)}};
  return result;
}

static inline sail_u320 u320_of_u128(const sail_u128 value) {
  sail_u320 result = {{
      value.limbs[0], value.limbs[1], UINT64_C(0), UINT64_C(0), UINT64_C(0)}};
  return result;
}

static inline sail_u320 u320_of_u256(const sail_u256 value) {
  sail_u320 result = {{
      value.limbs[0], value.limbs[1], value.limbs[2], value.limbs[3],
      UINT64_C(0)}};
  return result;
}

static inline uint64_t u320_to_u64(const sail_u320 value) {
  if ((value.limbs[1] | value.limbs[2] | value.limbs[3] | value.limbs[4])
      != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint64_t domain");
  }
  return value.limbs[0];
}

static inline sail_u128 u128_of_u320(const sail_u320 value) {
  if ((value.limbs[2] | value.limbs[3] | value.limbs[4]) != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint128_t domain");
  }
  sail_u128 result = {{value.limbs[0], value.limbs[1]}};
  return result;
}

static inline sail_u256 u256_of_u320(const sail_u320 value) {
  if (value.limbs[4] != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint256_t domain");
  }
  sail_u256 result = {{
      value.limbs[0], value.limbs[1], value.limbs[2], value.limbs[3]}};
  return result;
}

static inline bool eq_u320(const sail_u320 lhs, const sail_u320 rhs) {
  for (size_t i = 0; i < 5; ++i) {
    if (lhs.limbs[i] != rhs.limbs[i]) return false;
  }
  return true;
}

static inline bool u320_lt(const sail_u320 lhs, const sail_u320 rhs) {
  for (size_t i = 5; i-- > 0;) {
    if (lhs.limbs[i] != rhs.limbs[i]) return lhs.limbs[i] < rhs.limbs[i];
  }
  return false;
}

static inline sail_u320 u320_add(const sail_u320 lhs, const sail_u320 rhs) {
  sail_u320 result;
  uint64_t carry = UINT64_C(0);
  for (size_t i = 0; i < 5; ++i) {
    const unsigned __int128 sum =
        (unsigned __int128)lhs.limbs[i] + rhs.limbs[i] + carry;
    result.limbs[i] = (uint64_t)sum;
    carry = (uint64_t)(sum >> 64);
  }
  return result;
}

static inline sail_u320 u320_sub(const sail_u320 lhs, const sail_u320 rhs) {
  sail_u320 result;
  uint64_t borrow = UINT64_C(0);
  for (size_t i = 0; i < 5; ++i) {
    const uint64_t partial = lhs.limbs[i] - rhs.limbs[i];
    const uint64_t borrow1 = lhs.limbs[i] < rhs.limbs[i];
    result.limbs[i] = partial - borrow;
    const uint64_t borrow2 = partial < borrow;
    borrow = borrow1 | borrow2;
  }
  return result;
}

static inline sail_u320 u320_mul(const sail_u320 lhs, const sail_u320 rhs) {
  sail_u320 result = {{0}};
  for (size_t i = 0; i < 5; ++i) {
    unsigned __int128 carry = 0;
    for (size_t j = 0; i + j < 5; ++j) {
      const size_t k = i + j;
      const unsigned __int128 sum =
          (unsigned __int128)lhs.limbs[i] * rhs.limbs[j]
          + result.limbs[k] + carry;
      result.limbs[k] = (uint64_t)sum;
      carry = sum >> 64;
    }
  }
  return result;
}

static inline sail_u320 u320_identity(const sail_u320 value) {
  return value;
}

static inline sail_u320 u320_add_scalar(
    const sail_u320 lhs, const uint64_t rhs) {
  sail_u320 result = lhs;
  unsigned __int128 sum = (unsigned __int128)result.limbs[0] + rhs;
  result.limbs[0] = (uint64_t)sum;
  uint64_t carry = (uint64_t)(sum >> 64);
  for (size_t i = 1; i < 5 && carry != UINT64_C(0); ++i) {
    sum = (unsigned __int128)result.limbs[i] + carry;
    result.limbs[i] = (uint64_t)sum;
    carry = (uint64_t)(sum >> 64);
  }
  return result;
}

static inline sail_u320 u320_mul_scalar(
    const sail_u320 lhs, const uint64_t rhs) {
  sail_u320 result;
  unsigned __int128 carry = 0;
  for (size_t i = 0; i < 5; ++i) {
    const unsigned __int128 product =
        (unsigned __int128)lhs.limbs[i] * rhs + carry;
    result.limbs[i] = (uint64_t)product;
    carry = product >> 64;
  }
  return result;
}

/*
 * Select the widening conversion after specialization has fixed the final C
 * parameter type.  The specialization pass may narrow a function parameter
 * after arithmetic analysis, so baking the pre-specialization operand types
 * into a helper name would make the generated call stale.
 */
#define U320_SELECT_RHS(stem, rhs) \
  _Generic((rhs), \
      sail_u320: stem##_u320, \
      sail_u256: stem##_u256, \
      sail_u128: stem##_u128, \
      default: stem##_u64)

#define U320_SELECT_BINARY(operation, lhs, rhs) \
  _Generic((lhs), \
      sail_u320: U320_SELECT_RHS(u320_##operation##_u320, rhs), \
      sail_u256: U320_SELECT_RHS(u320_##operation##_u256, rhs), \
      sail_u128: U320_SELECT_RHS(u320_##operation##_u128, rhs), \
      default: U320_SELECT_RHS(u320_##operation##_u64, rhs))

#define u320_add_widen(lhs, rhs) \
  U320_SELECT_BINARY(add, lhs, rhs)((lhs), (rhs))

#define u320_mul_widen(lhs, rhs) \
  U320_SELECT_BINARY(mul, lhs, rhs)((lhs), (rhs))

static inline sail_u320 u320_add_u320_u320(
    const sail_u320 lhs, const sail_u320 rhs) {
  return u320_add(lhs, rhs);
}

static inline sail_u320 u320_add_u320_u256(
    const sail_u320 lhs, const sail_u256 rhs) {
  return u320_add(lhs, u320_of_u256(rhs));
}

static inline sail_u320 u320_add_u320_u128(
    const sail_u320 lhs, const sail_u128 rhs) {
  return u320_add(lhs, u320_of_u128(rhs));
}

static inline sail_u320 u320_add_u320_u64(
    const sail_u320 lhs, const uint64_t rhs) {
  return u320_add_scalar(lhs, rhs);
}

static inline sail_u320 u320_add_u256_u320(
    const sail_u256 lhs, const sail_u320 rhs) {
  return u320_add(rhs, u320_of_u256(lhs));
}

static inline sail_u320 u320_add_u256_u256(
    const sail_u256 lhs, const sail_u256 rhs) {
  return u320_add(u320_of_u256(lhs), u320_of_u256(rhs));
}

static inline sail_u320 u320_add_u256_u128(
    const sail_u256 lhs, const sail_u128 rhs) {
  return u320_add(u320_of_u256(lhs), u320_of_u128(rhs));
}

static inline sail_u320 u320_add_u128_u256(
    const sail_u128 lhs, const sail_u256 rhs) {
  return u320_add_u256_u128(rhs, lhs);
}

static inline sail_u320 u320_add_u256_u64(
    const sail_u256 lhs, const uint64_t rhs) {
  return u320_add_scalar(u320_of_u256(lhs), rhs);
}

static inline sail_u320 u320_add_u64_u256(
    const uint64_t lhs, const sail_u256 rhs) {
  return u320_add_u256_u64(rhs, lhs);
}

static inline sail_u320 u320_add_u128_u128(
    const sail_u128 lhs, const sail_u128 rhs) {
  return u320_add(u320_of_u128(lhs), u320_of_u128(rhs));
}

static inline sail_u320 u320_add_u128_u320(
    const sail_u128 lhs, const sail_u320 rhs) {
  return u320_add(rhs, u320_of_u128(lhs));
}

static inline sail_u320 u320_add_u128_u64(
    const sail_u128 lhs, const uint64_t rhs) {
  return u320_add_scalar(u320_of_u128(lhs), rhs);
}

static inline sail_u320 u320_add_u64_u128(
    const uint64_t lhs, const sail_u128 rhs) {
  return u320_add_u128_u64(rhs, lhs);
}

static inline sail_u320 u320_add_u64_u64(
    const uint64_t lhs, const uint64_t rhs) {
  return u320_add_scalar(u320_of_u64(lhs), rhs);
}

static inline sail_u320 u320_add_u64_u320(
    const uint64_t lhs, const sail_u320 rhs) {
  return u320_add_scalar(rhs, lhs);
}

static inline sail_u320 u320_mul_u320_u320(
    const sail_u320 lhs, const sail_u320 rhs) {
  return u320_mul(lhs, rhs);
}

static inline sail_u320 u320_mul_u320_u256(
    const sail_u320 lhs, const sail_u256 rhs) {
  return u320_mul(lhs, u320_of_u256(rhs));
}

static inline sail_u320 u320_mul_u320_u128(
    const sail_u320 lhs, const sail_u128 rhs) {
  return u320_mul(lhs, u320_of_u128(rhs));
}

static inline sail_u320 u320_mul_u320_u64(
    const sail_u320 lhs, const uint64_t rhs) {
  return u320_mul_scalar(lhs, rhs);
}

static inline sail_u320 u320_mul_u256_u320(
    const sail_u256 lhs, const sail_u320 rhs) {
  return u320_mul(rhs, u320_of_u256(lhs));
}

static inline sail_u320 u320_mul_u256_u256(
    const sail_u256 lhs, const sail_u256 rhs) {
  return u320_mul(u320_of_u256(lhs), u320_of_u256(rhs));
}

static inline sail_u320 u320_mul_u256_u128(
    const sail_u256 lhs, const sail_u128 rhs) {
  return u320_mul(u320_of_u256(lhs), u320_of_u128(rhs));
}

static inline sail_u320 u320_mul_u128_u256(
    const sail_u128 lhs, const sail_u256 rhs) {
  return u320_mul_u256_u128(rhs, lhs);
}

static inline sail_u320 u320_mul_u256_u64(
    const sail_u256 lhs, const uint64_t rhs) {
  return u320_mul_scalar(u320_of_u256(lhs), rhs);
}

static inline sail_u320 u320_mul_u64_u256(
    const uint64_t lhs, const sail_u256 rhs) {
  return u320_mul_u256_u64(rhs, lhs);
}

static inline sail_u320 u320_mul_u128_u128(
    const sail_u128 lhs, const sail_u128 rhs) {
  return u320_mul(u320_of_u128(lhs), u320_of_u128(rhs));
}

static inline sail_u320 u320_mul_u128_u320(
    const sail_u128 lhs, const sail_u320 rhs) {
  return u320_mul(rhs, u320_of_u128(lhs));
}

static inline sail_u320 u320_mul_u128_u64(
    const sail_u128 lhs, const uint64_t rhs) {
  return u320_mul_scalar(u320_of_u128(lhs), rhs);
}

static inline sail_u320 u320_mul_u64_u128(
    const uint64_t lhs, const sail_u128 rhs) {
  return u320_mul_u128_u64(rhs, lhs);
}

static inline sail_u320 u320_mul_u64_u64(
    const uint64_t lhs, const uint64_t rhs) {
  return u320_mul_scalar(u320_of_u64(lhs), rhs);
}

static inline sail_u320 u320_mul_u64_u320(
    const uint64_t lhs, const sail_u320 rhs) {
  return u320_mul_scalar(rhs, lhs);
}

static inline sail_u256 u256_sub_u320(
    const sail_u256 lhs, const sail_u320 rhs) {
  return u256_of_u320(u320_sub(u320_of_u256(lhs), rhs));
}

static inline sail_u128 u128_sub_u320(
    const sail_u128 lhs, const sail_u320 rhs) {
  return u128_of_u320(u320_sub(u320_of_u128(lhs), rhs));
}

static inline uint64_t u64_sub_u320(
    const uint64_t lhs, const sail_u320 rhs) {
  return u320_to_u64(u320_sub(u320_of_u64(lhs), rhs));
}

/* Base-2^64 long division for the common five-by-one-limb shape. */
static inline void u320_divrem_u64(
    const sail_u320 dividend,
    const uint64_t divisor,
    sail_u320 *quotient,
    uint64_t *remainder) {
  sail_u320 q = {{0}};
  uint64_t rem = UINT64_C(0);
  for (size_t i = 5; i-- > 0;) {
    const unsigned __int128 partial =
        ((unsigned __int128)rem << 64) | dividend.limbs[i];
    q.limbs[i] = (uint64_t)(partial / divisor);
    rem = (uint64_t)(partial % divisor);
  }
  if (quotient != NULL) *quotient = q;
  if (remainder != NULL) *remainder = rem;
}

static inline sail_u320 u320_div_u64(
    const sail_u320 dividend, const uint64_t divisor) {
  sail_u320 result;
  u320_divrem_u64(dividend, divisor, &result, NULL);
  return result;
}

static inline uint64_t u320_mod_u64(
    const sail_u320 dividend, const uint64_t divisor) {
  uint64_t result;
  u320_divrem_u64(dividend, divisor, NULL, &result);
  return result;
}

static inline bool u320_is_zero(const sail_u320 value) {
  return (value.limbs[0] | value.limbs[1] | value.limbs[2]
          | value.limbs[3] | value.limbs[4]) == UINT64_C(0);
}

static inline bool u320_power_of_two_shift(
    const sail_u320 value, uint32_t *shift) {
  uint32_t found = UINT32_MAX;
  for (uint32_t i = 0; i < 5; ++i) {
    const uint64_t limb = value.limbs[i];
    if (limb == UINT64_C(0)) continue;
    if ((limb & (limb - UINT64_C(1))) != UINT64_C(0) || found != UINT32_MAX) {
      return false;
    }
    found = i * 64U + (uint32_t)__builtin_ctzll(limb);
  }
  if (found == UINT32_MAX) return false;
  *shift = found;
  return true;
}

static inline sail_u320 u320_shr(const sail_u320 value, const uint32_t shift) {
  sail_u320 result = {{0}};
  if (shift >= 320U) return result;
  const uint32_t words = shift / 64U;
  const uint32_t bits = shift % 64U;
  for (uint32_t out = 0; out + words < 5U; ++out) {
    const uint32_t in = out + words;
    result.limbs[out] = value.limbs[in] >> bits;
    if (bits != 0U && in + 1U < 5U) {
      result.limbs[out] |= value.limbs[in + 1U] << (64U - bits);
    }
  }
  return result;
}

static inline sail_u320 u320_mod_power_of_two(
    const sail_u320 value, const uint32_t shift) {
  if (shift >= 320U) return value;
  sail_u320 result = value;
  const uint32_t word = shift / 64U;
  const uint32_t bits = shift % 64U;
  if (bits == 0U) {
    for (uint32_t i = word; i < 5U; ++i) result.limbs[i] = UINT64_C(0);
  } else {
    result.limbs[word] &= (UINT64_C(1) << bits) - UINT64_C(1);
    for (uint32_t i = word + 1U; i < 5U; ++i) {
      result.limbs[i] = UINT64_C(0);
    }
  }
  return result;
}

/* The general fallback is a fixed-width restoring division.  The generated
 * EVM recurrence takes the one-limb fast path at runtime; the fallback keeps
 * the representation complete for other proved U320 expressions. */
static inline void u320_divrem(
    const sail_u320 dividend,
    const sail_u320 divisor,
    sail_u320 *quotient,
    sail_u320 *remainder) {
  if (u320_is_zero(divisor)) {
    sail_native_conversion_failure("division by zero");
  }
  if ((divisor.limbs[1] | divisor.limbs[2]
       | divisor.limbs[3] | divisor.limbs[4]) == UINT64_C(0)) {
    sail_u320 q;
    uint64_t r;
    u320_divrem_u64(dividend, divisor.limbs[0], &q, &r);
    if (quotient != NULL) *quotient = q;
    if (remainder != NULL) *remainder = u320_of_u64(r);
    return;
  }
  uint32_t shift;
  if (u320_power_of_two_shift(divisor, &shift)) {
    if (quotient != NULL) *quotient = u320_shr(dividend, shift);
    if (remainder != NULL) *remainder = u320_mod_power_of_two(dividend, shift);
    return;
  }

  sail_u320 q = {{0}};
  sail_u320 rem = {{0}};
  for (uint32_t bit = 320U; bit-- > 0U;) {
    const uint64_t carry = rem.limbs[4] >> 63;
    for (uint32_t i = 4U; i > 0U; --i) {
      rem.limbs[i] = (rem.limbs[i] << 1) | (rem.limbs[i - 1U] >> 63);
    }
    rem.limbs[0] =
        (rem.limbs[0] << 1)
        | ((dividend.limbs[bit / 64U] >> (bit % 64U)) & UINT64_C(1));
    if (carry != UINT64_C(0) || !u320_lt(rem, divisor)) {
      rem = u320_sub(rem, divisor);
      q.limbs[bit / 64U] |= UINT64_C(1) << (bit % 64U);
    }
  }
  if (quotient != NULL) *quotient = q;
  if (remainder != NULL) *remainder = rem;
}

static inline sail_u320 u320_div(
    const sail_u320 dividend, const sail_u320 divisor) {
  sail_u320 result;
  u320_divrem(dividend, divisor, &result, NULL);
  return result;
}

static inline sail_u320 u320_mod(
    const sail_u320 dividend, const sail_u320 divisor) {
  sail_u320 result;
  u320_divrem(dividend, divisor, NULL, &result);
  return result;
}
|}
      in
      let generic_sail_int_helpers =
        string
          {|
static inline sail_u320 u320_of_sail_int(const sail_int value) {
  sail_u320 result = {{0}};
  sail_int_to_u64_array(result.limbs, 5, value);
  return result;
}

static inline void u320_unsigned(sail_int *result, const sail_u320 value) {
  sail_int_from_u64_array(result, value.limbs, 5);
}
|}
      in
      let helpers = base_helpers ^^ if !emit_generic_sail_int_helpers then generic_sail_int_helpers else empty in
      [TypeDeclaration typedef; StaticFunctionDefinition helpers]
    )

  let codegen_fixed_bytes length =
    let id = mk_id ("__sail_c_repr_fixed_bytes_" ^ string_of_int length) in
    if IdSet.mem id !generated then []
    else (
      generated := IdSet.add id !generated;
      let ctyp = sprintf "sail_fixed_bytes_%d" length in
      let type_name = sprintf "fixed_bytes_%d" length in
      let guard = sprintf "SAIL_FIXED_BYTES_%d_DEFINED" length in
      let typedef =
        ksprintf string "#ifndef %s\n#define %s\ntypedef struct { uint8_t bytes[%d]; } %s;\n#endif" guard guard length
          ctyp
      in
      let base_helpers =
        ksprintf string
          {|
static inline %s %s_zero(void) {
  %s result = {{0}};
  return result;
}

static inline bool eq_%s(const %s lhs, const %s rhs) {
  return memcmp(lhs.bytes, rhs.bytes, %d) == 0;
}
|}
          ctyp type_name ctyp type_name ctyp ctyp length
      in
      let byte_u256_helpers =
        if length > 32 then empty
        else
          ksprintf string
            {|

#ifndef SAIL_U256_DEFINED
#define SAIL_U256_DEFINED
typedef struct { uint64_t limbs[4]; } sail_u256;
#endif

static inline sail_u256 u256_from_%s(const %s value) {
  sail_u256 result = {{0}};
  for (size_t i = 0; i < %d; ++i) {
    result.limbs[i >> 3] |= ((uint64_t)value.bytes[i]) << ((i & 7) * 8);
  }
  return result;
}

static inline %s %s_from_u256(const sail_u256 value) {
  %s result;
  for (size_t i = 0; i < %d; ++i) {
    result.bytes[i] = (uint8_t)(value.limbs[i >> 3] >> ((i & 7) * 8));
  }
  return result;
}
|}
            type_name ctyp length ctyp type_name ctyp length
      in
      let generic_helpers =
        ksprintf string
          {|

static inline %s vector_init_%s(const sail_int length_arg, const uint64_t elem) {
  (void)length_arg;
  %s result;
  for (size_t i = 0; i < %d; ++i) result.bytes[i] = (uint8_t)elem;
  return result;
}

static inline %s undefined_vector_%s(const sail_int length_arg, const uint64_t elem) {
  return vector_init_%s(length_arg, elem);
}

static inline %s vector_update_%s(%s value, const sail_int index, const uint64_t elem) {
  const uint64_t i = sail_int_get_ui(index);
  if (i < %d) value.bytes[i] = (uint8_t)elem;
  return value;
}

static inline uint64_t vector_access_%s(const %s value, const sail_int index) {
  const uint64_t i = sail_int_get_ui(index);
  return i < %d ? (uint64_t)value.bytes[i] : UINT64_C(0);
}

static inline void length_%s(sail_int *result, const %s value) {
  (void)value;
  mpz_set_ui(*result, %d);
}
|}
          ctyp type_name ctyp length ctyp type_name type_name ctyp type_name ctyp length type_name ctyp length type_name
          ctyp length
      in
      let native_signed_index_helpers =
        ksprintf string
          {|
static inline %s internal_vector_init_%s(const int64_t length_arg) {
  (void)length_arg;
  return %s_zero();
}

static inline %s internal_vector_update_%s(
    %s value, const int64_t index, const uint64_t elem) {
  if (index >= 0 && index < %d) value.bytes[index] = (uint8_t)elem;
  return value;
}

static inline uint64_t fast_vector_access_%s(const %s value, const int64_t index) {
  return index >= 0 && index < %d ? (uint64_t)value.bytes[index] : UINT64_C(0);
}
|}
          ctyp type_name type_name ctyp type_name ctyp length type_name ctyp length
      in
      let native_unsigned_index_helpers =
        ksprintf string
          {|
static inline %s fast_unsigned_vector_update_%s(
    %s value, const uint64_t index, const uint64_t elem) {
  if (index < %d) value.bytes[index] = (uint8_t)elem;
  return value;
}

static inline uint64_t fast_unsigned_vector_access_%s(
    const %s value, const uint64_t index) {
  return index < %d ? (uint64_t)value.bytes[index] : UINT64_C(0);
}
|}
          ctyp type_name ctyp length type_name ctyp length
      in
      let native_init_helpers =
        ksprintf string
          {|
static inline %s fast_vector_init_%s(const int64_t length_arg, const uint64_t elem) {
  (void)length_arg;
  %s result;
  for (size_t i = 0; i < %d; ++i) result.bytes[i] = (uint8_t)elem;
  return result;
}

static inline %s fast_unsigned_vector_init_%s(const uint64_t length_arg, const uint64_t elem) {
  (void)length_arg;
  %s result;
  for (size_t i = 0; i < %d; ++i) result.bytes[i] = (uint8_t)elem;
  return result;
}
|}
          ctyp type_name ctyp length ctyp type_name ctyp length
      in
      let helpers =
        base_helpers ^^ byte_u256_helpers
        ^^ (if !emit_generic_sail_int_helpers then generic_helpers else empty)
        ^^ native_signed_index_helpers ^^ native_unsigned_index_helpers ^^ native_init_helpers
      in
      [TypeDeclaration typedef; StaticFunctionDefinition helpers]
    )

  let codegen_tup ctx ctyps =
    let ctyp = CT_tup ctyps in
    let key = mk_id ("tuple_" ^ string_of_ctyp ctyp) in
    let id = if Config.no_mangle then mk_id (readable_ctyp_name ctyp) else key in
    if IdSet.mem key !generated then []
    else (
      let _, fields =
        List.fold_left
          (fun (n, fields) ctyp -> (n + 1, Bindings.add (mk_id ("tup" ^ string_of_int n)) ctyp fields))
          (0, Bindings.empty) ctyps
      in
      generated := IdSet.add key !generated;
      codegen_type_def
        { ctx with records = Bindings.add id ([], fields) ctx.records }
        (CTD_struct (id, [], Bindings.bindings fields))
    )

  let codegen_list ctx ctyp =
    let open Printf in
    let list_ctyp = CT_list ctyp in
    let key = mk_id (string_of_ctyp list_ctyp) in
    let id = if Config.no_mangle then mk_id (readable_ctyp_name list_ctyp) else key in
    if IdSet.mem key !generated then []
    else (
      generated := IdSet.add key !generated;
      let codegen_node =
        ksprintf string "struct node_%s {\n  unsigned int rc;\n  %s hd;\n  struct node_%s *tl;\n};\n" (sgen_id id)
          (sgen_ctyp ctyp) (sgen_id id)
        ^^ string (sprintf "typedef struct node_%s *%s;" (sgen_id id) (sgen_id id))
      in

      let codegen_list_init =
        let create = sail_create (sgen_id id) "%s *rop" (sgen_id id) in
        separate space [string "static void"; create; string "{ *rop = NULL; }"]
      in

      let codegen_list_clear =
        let kill = sail_kill (sgen_id id) "%s *rop" (sgen_id id) in
        separate space [string "static void"; kill; char '{']
        ^^ hardline ^^ string "  if (*rop == NULL) return;\n" ^^ string "  if ((*rop)->rc >= 1) {\n"
        ^^ string "    (*rop)->rc -= 1;\n" ^^ string "  }\n"
        ^^ ksprintf string "  %s node = *rop;\n" (sgen_id id)
        ^^ string "  while (node != NULL && node->rc == 0) {\n"
        ^^ ( if is_stack_ctyp ctx ctyp then empty
             else sail_kill ~prefix:"    " ~suffix:";\n" (sgen_ctyp_name ctyp) "&node->hd"
           )
        ^^ ksprintf string "    %s next = node->tl;\n" (sgen_id id)
        ^^ string "    sail_free(node);\n" ^^ string "    node = next;\n"
        ^^ ksprintf string "    internal_dec_%s(node);\n" (sgen_id id)
        ^^ string "  }\n" ^^ string "}"
      in

      let codegen_list_recreate =
        c_function ~return:"static void"
          (sail_recreate (sgen_id id) "%s *rop" (sgen_id id))
          [sail_kill ~suffix:";" (sgen_id id) "rop"; string "*rop = NULL;"]
      in

      let codegen_inc_reference_count =
        string (sprintf "static void internal_inc_%s(%s l) {\n" (sgen_id id) (sgen_id id))
        ^^ string "  if (l == NULL) return;\n" ^^ string "  l->rc += 1;\n" ^^ string "}"
      in

      let codegen_dec_reference_count =
        string (sprintf "static void internal_dec_%s(%s l) {\n" (sgen_id id) (sgen_id id))
        ^^ string "  if (l == NULL) return;\n" ^^ string "  l->rc -= 1;\n" ^^ string "}"
      in

      let codegen_list_copy =
        let ty = sgen_id id in
        c_function ~return:"static void" (sail_copy ty "%s *rop, %s op" ty ty)
          [ksprintf c_stmt "internal_inc_%s(op)" ty; sail_kill ~suffix:";" ty "rop"; c_stmt "*rop = op"]
      in

      let codegen_cons =
        let cons_id = mk_id ("cons#" ^ string_of_ctyp ctyp) in
        ksprintf string "static void %s(%s *rop, %s x, %s xs) {\n" (sgen_function_id cons_id) (sgen_id id)
          (sgen_const_ctyp ctyp) (sgen_id id)
        ^^ string "  bool same = *rop == xs;\n"
        ^^ ksprintf string "  *rop = sail_new(struct node_%s);\n" (sgen_id id)
        ^^ string "  (*rop)->rc = 1;\n"
        ^^ ( if is_stack_ctyp ctx ctyp then string "  (*rop)->hd = x;\n"
             else
               sail_create ~prefix:"  " ~suffix:";\n" (sgen_ctyp_name ctyp) "&(*rop)->hd"
               ^^ sail_copy ~prefix:"  " ~suffix:";\n" (sgen_ctyp_name ctyp) "&(*rop)->hd, x"
           )
        ^^ ksprintf string "  if (!same) internal_inc_%s(xs);\n" (sgen_id id)
        ^^ string "  (*rop)->tl = xs;\n" ^^ string "}"
      in

      let codegen_pick =
        if is_stack_ctyp ctx ctyp then
          c_function
            ~return:(sprintf "static %s" (sgen_ctyp ctyp))
            (ksprintf string "pick_%s(const %s xs)" (sgen_ctyp_name ctyp) (sgen_id id))
            [c_return (string "xs->hd")]
        else
          c_function ~return:"static void"
            (ksprintf string "pick_%s(%s *x, const %s xs)" (sgen_ctyp_name ctyp) (sgen_ctyp ctyp) (sgen_id id))
            [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "x, xs->hd"]
      in

      let codegen_list_equal =
        let equal_hd = codegen_equal ctyp "op1->hd" "op2->hd" in
        let equal_tl = sail_equal (sgen_id id) "op1->tl, op2->tl" in
        c_function ~return:"static bool"
          (sail_equal (sgen_id id) "const %s op1, const %s op2" (sgen_id id) (sgen_id id))
          [
            string "if (op1 == NULL && op2 == NULL) { return true; };";
            string "if (op1 == NULL || op2 == NULL) { return false; };";
            c_return (separate space [equal_hd; string "&&"; equal_tl]);
          ]
      in

      let codegen_list_undefined =
        ksprintf string "static void UNDEFINED(%s)(%s *rop, %s u) {\n" (sgen_id id) (sgen_id id) (sgen_ctyp ctyp)
        ^^ ksprintf string "  *rop = NULL;\n" ^^ string "}"
      in
      [
        TypeDeclaration codegen_node;
        StaticFunctionDefinition codegen_list_init;
        StaticFunctionDefinition codegen_inc_reference_count;
        StaticFunctionDefinition codegen_dec_reference_count;
        StaticFunctionDefinition codegen_list_clear;
        StaticFunctionDefinition codegen_list_recreate;
        StaticFunctionDefinition codegen_list_copy;
        StaticFunctionDefinition codegen_cons;
        StaticFunctionDefinition codegen_pick;
        StaticFunctionDefinition codegen_list_equal;
        StaticFunctionDefinition codegen_list_undefined;
      ]
    )

  (* Generate functions for working with non-bit vectors of some specific type. *)
  let codegen_fixed_vector ctx length ctyp =
    let open Printf in
    let vector_ctyp = CT_fvector (length, ctyp) in
    let key = mk_id (string_of_ctyp vector_ctyp) in
    let id = if Config.no_mangle then mk_id (readable_ctyp_name vector_ctyp) else key in
    if IdSet.mem key !generated then []
    else (
      let name = sgen_id id in
      let stack_elem = is_stack_ctyp ctx ctyp in
      let guard = "SAIL_FIXED_VECTOR_" ^ String.uppercase_ascii name ^ "_DEFINED" in
      let typedef =
        ksprintf string "#ifndef %s\n#define %s\n" guard guard
        ^^ ksprintf string "typedef struct %s {\n  size_t len;\n  %s data[%d];\n} %s;\n#endif" name (sgen_ctyp ctyp)
             length name
      in
      let fill index elem =
        if stack_elem then ksprintf c_stmt "vec->data[%s] = %s" index elem
        else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&vec->data[%s], %s" index elem
      in
      let initialize_elements =
        if stack_elem then []
        else
          [c_for (ksprintf string "(size_t i = 0; i < %d; ++i)" length)
             [sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[i]"]]
      in
      let clear_elements =
        if stack_elem then []
        else
          [c_for (ksprintf string "(size_t i = 0; i < %d; ++i)" length)
             [sail_kill ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[i]"]]
      in
      let create =
        c_function ~return:"static void" (sail_create name "%s *rop" name)
          ([ksprintf c_stmt "rop->len = %d" length] @ initialize_elements)
      in
      let clear = c_function ~return:"static void" (sail_kill name "%s *rop" name) clear_elements in
      let recreate =
        c_function ~return:"static void" (sail_recreate name "%s *rop" name)
          [sail_kill ~suffix:";" name "rop"; sail_create ~suffix:";" name "rop"]
      in
      let copy =
        c_function ~return:"static void" (sail_copy name "%s *rop, const %s op" name name)
          ( if stack_elem then [c_stmt "*rop = op"]
            else
              [c_stmt "rop->len = op.len";
               c_for (ksprintf string "(size_t i = 0; i < %d; ++i)" length)
                 [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[i], op.data[i]"]]
          )
      in
      let init name_suffix length_type length_expr =
        if stack_elem then
          c_function ~return:("static " ^ name)
            (ksprintf string "%s_%s(const %s n, %s elem)" name_suffix name length_type (sgen_ctyp ctyp))
            [ksprintf c_stmt "%s vec" name; c_stmt ("size_t m = (size_t)" ^ length_expr); c_stmt "vec.len = m";
             c_for (string "(size_t i = 0; i < m; ++i)") [c_stmt "vec.data[i] = elem"]; c_stmt "return vec"]
        else
          c_function ~return:"static void"
            (ksprintf string "%s_%s(%s *vec, const %s n, %s elem)" name_suffix name name length_type
               (sgen_ctyp ctyp))
            [c_stmt ("size_t m = (size_t)" ^ length_expr); c_stmt "vec->len = m";
             c_for (string "(size_t i = 0; i < m; ++i)") [fill "i" "elem"]]
      in
      let vector_init =
        c_function ~return:"static void"
          (ksprintf string "vector_init_%s(%s *vec, sail_int n, %s elem)" name name (sgen_ctyp ctyp))
          [c_stmt "size_t m = (size_t)sail_int_get_ui(n)"; c_stmt "vec->len = m";
           c_for (string "(size_t i = 0; i < m; ++i)") [fill "i" "elem"]]
      in
      let update function_name index_type index_expr =
        if stack_elem then
          c_function ~return:("static " ^ name)
            (ksprintf string "%s_%s(%s op, const %s n, %s elem)" function_name name name index_type
               (sgen_ctyp ctyp))
            [c_stmt ("size_t m = (size_t)" ^ index_expr); c_stmt "op.data[m] = elem"; c_stmt "return op"]
        else
          c_function ~return:"static void"
            (ksprintf string "%s_%s(%s *rop, %s op, const %s n, %s elem)" function_name name name name index_type
               (sgen_ctyp ctyp))
            [sail_copy ~suffix:";" name "rop, op"; c_stmt ("size_t m = (size_t)" ^ index_expr);
             sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[m], elem"]
      in
      let vector_update =
        c_function ~return:"static void"
          (ksprintf string "vector_update_%s(%s *rop, %s op, sail_int n, %s elem)" name name name (sgen_ctyp ctyp))
          ([if stack_elem then c_stmt "*rop = op" else sail_copy ~suffix:";" name "rop, op";
            c_stmt "size_t m = (size_t)sail_int_get_ui(n)"]
          @ [if stack_elem then c_stmt "rop->data[m] = elem"
             else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[m], elem"])
      in
      let access function_name index_type =
        if stack_elem then
          c_function ~return:("static " ^ sgen_ctyp ctyp)
            (ksprintf string "%s_%s(%s op, %s n)" function_name name name index_type)
            [c_stmt "return op.data[(size_t)n]"]
        else
          c_function ~return:"static void"
            (ksprintf string "%s_%s(%s *rop, %s op, %s n)" function_name name (sgen_ctyp ctyp) name index_type)
            [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "rop, op.data[(size_t)n]"]
      in
      let vector_access =
        if stack_elem then
          c_function ~return:("static " ^ sgen_ctyp ctyp)
            (ksprintf string "vector_access_%s(%s op, sail_int n)" name name)
            [c_stmt "return op.data[(size_t)sail_int_get_ui(n)]"]
        else
          c_function ~return:"static void"
            (ksprintf string "vector_access_%s(%s *rop, %s op, sail_int n)" name (sgen_ctyp ctyp) name)
            [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "rop, op.data[(size_t)sail_int_get_ui(n)]"]
      in
      let internal_init =
        if stack_elem then
          c_function ~return:("static " ^ name)
            (ksprintf string "internal_vector_init_%s(const int64_t len)" name)
            [ksprintf c_stmt "%s rop" name; c_stmt "rop.len = (size_t)len"; c_stmt "return rop"]
        else
          c_function ~return:"static void"
            (ksprintf string "internal_vector_init_%s(%s *rop, const int64_t len)" name name)
            [c_stmt "rop->len = (size_t)len"]
      in
      let internal_update = update "internal_vector_update" "int64_t" "n" in
      let equal =
        c_function ~return:"static bool" (sail_equal name "const %s op1, const %s op2" name name)
          [c_stmt "if (op1.len != op2.len) return false"; c_stmt "bool result = true";
           c_for (string "(size_t i = 0; i < op1.len; ++i)")
             [c_assign (string "result") "&=" (codegen_equal ctyp "op1.data[i]" "op2.data[i]")];
           c_stmt "return result"]
      in
      let undefined =
        c_function ~return:"static void"
          (ksprintf string "undefined_vector_%s(%s *rop, sail_int len, %s elem)" name name (sgen_ctyp ctyp))
          [c_stmt "size_t m = (size_t)sail_int_get_ui(len)"; c_stmt "rop->len = m";
           c_for (string "(size_t i = 0; i < m; ++i)")
             [if stack_elem then c_stmt "rop->data[i] = elem"
              else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[i], elem"]]
      in
      let vector_length =
        c_function ~return:"static void" (ksprintf string "length_%s(sail_int *rop, %s op)" name name)
          [c_stmt "mpz_set_ui(*rop, (unsigned long int)op.len)"]
      in
      generated := IdSet.add key !generated;
      [TypeDeclaration typedef]
      @ (if stack_elem then [] else List.map (fun d -> StaticFunctionDefinition d) [create; clear; recreate; copy])
      @ (if !emit_generic_sail_int_helpers then
           List.map (fun d -> StaticFunctionDefinition d) [vector_init; vector_access; vector_update; undefined; vector_length]
         else [])
      @ List.map (fun d -> StaticFunctionDefinition d)
          [init "fast_vector_init" "int64_t" "n"; init "fast_unsigned_vector_init" "uint64_t" "n";
           access "fast_vector_access" "int64_t"; access "fast_unsigned_vector_access" "uint64_t";
           update "fast_vector_update" "int64_t" "n";
           update "fast_unsigned_vector_update" "uint64_t" "n"; equal; internal_update; internal_init]
    )

  let codegen_vector ctx ctyp =
    let open Printf in
    let vector_ctyp = CT_vector ctyp in
    let key = mk_id (string_of_ctyp vector_ctyp) in
    let id = if Config.no_mangle then mk_id (readable_ctyp_name vector_ctyp) else key in
    if IdSet.mem key !generated then []
    else (
      let guard = "SAIL_VECTOR_" ^ String.uppercase_ascii (sgen_id id) ^ "_DEFINED" in
      let vector_typedef =
        ksprintf string "#ifndef %s\n#define %s\n" guard guard
        ^^ ksprintf string "struct %s {\n  size_t len;\n  %s *data;\n};\n" (sgen_id id) (sgen_ctyp ctyp)
        ^^ ksprintf string "typedef struct %s %s;\n#endif" (sgen_id id) (sgen_id id)
      in
      let vector_decl =
        c_function ~return:"static void"
          (sail_create (sgen_id id) "%s *rop" (sgen_id id))
          [c_stmt "rop->len = 0"; c_stmt "rop->data = NULL"]
      in
      let vector_init =
        c_function ~return:"static void"
          (ksprintf string "vector_init_%s(%s *vec, sail_int n, %s elem)" (sgen_id id) (sgen_id id) (sgen_ctyp ctyp))
          [
            sail_kill ~suffix:";" (sgen_id id) "vec";
            c_stmt "size_t m = (size_t)sail_int_get_ui(n)";
            c_stmt "vec->len = m";
            ksprintf c_stmt "vec->data = sail_new_array(%s, m)" (sgen_ctyp ctyp);
            c_for (string "(size_t i = 0; i < m; i++)")
              ( if is_stack_ctyp ctx ctyp then [c_stmt "(vec->data)[i] = elem"]
                else
                  [
                    sail_create ~suffix:";" (sgen_ctyp_name ctyp) "(vec->data) + i";
                    sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(vec->data) + i, elem";
                  ]
              );
          ]
      in
      let native_vector_init name length_type =
        c_function ~return:"static void"
          (ksprintf string "%s_%s(%s *vec, const %s n, %s elem)" name (sgen_id id) (sgen_id id) length_type
             (sgen_ctyp ctyp)
          )
          [
            sail_kill ~suffix:";" (sgen_id id) "vec";
            c_stmt "size_t m = (size_t)n";
            c_stmt "vec->len = m";
            ksprintf c_stmt "vec->data = sail_new_array(%s, m)" (sgen_ctyp ctyp);
            c_for (string "(size_t i = 0; i < m; i++)")
              ( if is_stack_ctyp ctx ctyp then [c_stmt "(vec->data)[i] = elem"]
                else
                  [
                    sail_create ~suffix:";" (sgen_ctyp_name ctyp) "(vec->data) + i";
                    sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(vec->data) + i, elem";
                  ]
              );
          ]
      in
      let fast_vector_init = native_vector_init "fast_vector_init" "int64_t" in
      let fast_unsigned_vector_init = native_vector_init "fast_unsigned_vector_init" "uint64_t" in
      let vector_set =
        c_function ~return:"static void"
          (sail_copy (sgen_id id) "%s *rop, %s op" (sgen_id id) (sgen_id id))
          [
            sail_kill ~suffix:";" (sgen_id id) "rop";
            c_stmt "rop->len = op.len";
            ksprintf c_stmt "rop->data = sail_new_array(%s, rop->len)" (sgen_ctyp ctyp);
            c_for (string "(int i = 0; i < op.len; i++)")
              ( if is_stack_ctyp ctx ctyp then [c_stmt "(rop->data)[i] = op.data[i]"]
                else
                  [
                    sail_create ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i";
                    sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i, op.data[i]";
                  ]
              );
          ]
      in
      let vector_clear =
        c_function ~return:"static void"
          (sail_kill (sgen_id id) "%s *rop" (sgen_id id))
          (( if is_stack_ctyp ctx ctyp then []
             else
               [
                 c_for
                   (string "(int i = 0; i < (rop->len); i++)")
                   [sail_kill ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i"];
               ]
           )
          @ [c_stmt "if (rop->data != NULL) sail_free(rop->data)"]
          )
      in
      let vector_reinit =
        c_function ~return:"static void"
          (sail_recreate (sgen_id id) "%s *rop" (sgen_id id))
          [sail_kill ~suffix:";" (sgen_id id) "rop"; sail_create ~suffix:";" (sgen_id id) "rop"]
      in
      let vector_update =
        c_function ~return:"static void"
          (ksprintf string "vector_update_%s(%s *rop, %s op, sail_int n, %s elem)" (sgen_id id) (sgen_id id)
             (sgen_id id) (sgen_ctyp ctyp)
          )
          [
            c_stmt "int m = sail_int_get_ui(n)";
            c_if_else (string "(rop->data == op.data)")
              [
                ( if is_stack_ctyp ctx ctyp then c_stmt "rop->data[m] = elem"
                  else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + m, elem"
                );
              ]
              [
                sail_copy ~suffix:";" (sgen_id id) "rop, op";
                ( if is_stack_ctyp ctx ctyp then c_stmt "rop->data[m] = elem"
                  else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + m, elem"
                );
              ];
          ]
      in
      let native_vector_update name index_type =
        c_function ~return:"static void"
          (ksprintf string "%s_%s(%s *rop, %s op, const %s n, %s elem)" name (sgen_id id) (sgen_id id) (sgen_id id)
             index_type (sgen_ctyp ctyp)
          )
          [
            c_stmt "size_t m = (size_t)n";
            c_if_else (string "(rop->data == op.data)")
              [
                ( if is_stack_ctyp ctx ctyp then c_stmt "rop->data[m] = elem"
                  else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + m, elem"
                );
              ]
              [
                sail_copy ~suffix:";" (sgen_id id) "rop, op";
                ( if is_stack_ctyp ctx ctyp then c_stmt "rop->data[m] = elem"
                  else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + m, elem"
                );
              ];
          ]
      in
      let fast_vector_update = native_vector_update "fast_vector_update" "int64_t" in
      let fast_unsigned_vector_update = native_vector_update "fast_unsigned_vector_update" "uint64_t" in
      let internal_vector_update =
        c_function ~return:"static void"
          (ksprintf string "internal_vector_update_%s(%s *rop, %s op, const int64_t n, %s elem)" (sgen_id id)
             (sgen_id id) (sgen_id id) (sgen_ctyp ctyp)
          )
          ( if is_stack_ctyp ctx ctyp then [c_stmt "rop->data[n] = elem"]
            else [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + n, elem"]
          )
      in
      let vector_access =
        if is_stack_ctyp ctx ctyp then
          c_function
            ~return:("static " ^ sgen_ctyp ctyp)
            (ksprintf string "vector_access_%s(%s op, sail_int n)" (sgen_id id) (sgen_id id))
            [c_stmt "int m = sail_int_get_ui(n)"; c_stmt "return op.data[m]"]
        else
          c_function ~return:"static void"
            (ksprintf string "vector_access_%s(%s *rop, %s op, sail_int n)" (sgen_id id) (sgen_ctyp ctyp) (sgen_id id))
            [c_stmt "int m = sail_int_get_ui(n)"; sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "rop, op.data[m]"]
      in
      let fast_vector_access =
        if is_stack_ctyp ctx ctyp then
          c_function
            ~return:("static " ^ sgen_ctyp ctyp)
            (ksprintf string "fast_vector_access_%s(%s op, int64_t n)" (sgen_id id) (sgen_id id))
            [c_stmt "return op.data[n]"]
        else
          c_function ~return:"static void"
            (ksprintf string "fast_vector_access_%s(%s *rop, %s op, int64_t n)" (sgen_id id) (sgen_ctyp ctyp)
               (sgen_id id)
            )
            [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "rop, op.data[n]"]
      in
      let fast_unsigned_vector_access =
        if is_stack_ctyp ctx ctyp then
          c_function
            ~return:("static " ^ sgen_ctyp ctyp)
            (ksprintf string "fast_unsigned_vector_access_%s(%s op, uint64_t n)" (sgen_id id) (sgen_id id))
            [c_stmt "return op.data[n]"]
        else
          c_function ~return:"static void"
            (ksprintf string "fast_unsigned_vector_access_%s(%s *rop, %s op, uint64_t n)" (sgen_id id) (sgen_ctyp ctyp)
               (sgen_id id)
            )
            [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "rop, op.data[n]"]
      in
      let internal_vector_init =
        c_function ~return:"static void"
          (ksprintf string "internal_vector_init_%s(%s *rop, const int64_t len)" (sgen_id id) (sgen_id id))
          ([c_stmt "rop->len = len"; ksprintf c_stmt "rop->data = sail_new_array(%s, len)" (sgen_ctyp ctyp)]
          @ c_cond_block
              (not (is_stack_ctyp ctx ctyp))
              [
                c_for (string "(int i = 0; i < len; i++)")
                  [sail_create ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i"];
              ]
          )
      in
      let vector_undefined =
        c_function ~return:"static void"
          (ksprintf string "undefined_vector_%s(%s *rop, sail_int len, %s elem)" (sgen_id id) (sgen_id id)
             (sgen_ctyp ctyp)
          )
          [
            c_stmt "rop->len = sail_int_get_ui(len)";
            ksprintf c_stmt "rop->data = sail_new_array(%s, rop->len)" (sgen_ctyp ctyp);
            c_for
              (string "(int i = 0; i < (rop->len); i++)")
              ( if is_stack_ctyp ctx ctyp then [c_stmt "(rop->data)[i] = elem"]
                else
                  [
                    sail_create ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i";
                    sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "(rop->data) + i, elem";
                  ]
              );
          ]
      in
      let vector_equal =
        c_function ~return:"static bool"
          (sail_equal (sgen_id id) "const %s op1, const %s op2" (sgen_id id) (sgen_id id))
          [
            c_stmt "if (op1.len != op2.len) return false";
            c_stmt "bool result = true";
            c_for
              (string "(int i = 0; i < op1.len; i++)")
              [c_assign (string "result") "&=" (codegen_equal ctyp "op1.data[i]" "op2.data[i]")];
            c_stmt "return result";
          ]
      in
      let vector_length =
        c_function ~return:"static void"
          (ksprintf string "length_%s(sail_int *rop, %s op)" (sgen_id id) (sgen_id id))
          [c_stmt "mpz_set_ui(*rop, (unsigned long int)(op.len))"]
      in
      generated := IdSet.add key !generated;
      [TypeDeclaration vector_typedef; StaticFunctionDefinition vector_decl; StaticFunctionDefinition vector_clear]
      @ (if !emit_generic_sail_int_helpers then [StaticFunctionDefinition vector_init] else [])
      @ [
          StaticFunctionDefinition fast_vector_init;
          StaticFunctionDefinition fast_unsigned_vector_init;
          StaticFunctionDefinition vector_reinit;
        ]
      @ ( if !emit_generic_sail_int_helpers then
            [StaticFunctionDefinition vector_undefined; StaticFunctionDefinition vector_access]
          else []
        )
      @ [
          StaticFunctionDefinition fast_vector_access;
          StaticFunctionDefinition fast_unsigned_vector_access;
          StaticFunctionDefinition vector_set;
        ]
      @ (if !emit_generic_sail_int_helpers then [StaticFunctionDefinition vector_update] else [])
      @ [
          StaticFunctionDefinition fast_vector_update;
          StaticFunctionDefinition fast_unsigned_vector_update;
          StaticFunctionDefinition vector_equal;
        ]
      @ (if !emit_generic_sail_int_helpers then [StaticFunctionDefinition vector_length] else [])
      @ [StaticFunctionDefinition internal_vector_update; StaticFunctionDefinition internal_vector_init]
    )

  let is_decl = function I_aux (I_decl _, _) -> true | _ -> false

  let codegen_decl = function
    | I_aux (I_decl (ctyp, id), _) -> string (Printf.sprintf "%s %s;" (sgen_ctyp ctyp) (sgen_name id))
    | _ -> assert false

  let codegen_alloc ctx = function
    | I_aux (I_decl (ctyp, _), _) when is_stack_ctyp ctx ctyp -> empty
    | I_aux (I_decl (ctyp, id), _) -> sail_create ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | _ -> assert false

  (* Generate C code for a global register, constant (let), function definition, etc. *)
  let codegen_def' ctx (CDEF_aux (aux, _)) =
    match aux with
    | CDEF_register (id, ctyp, _) ->
        let definition =
          VariableDefinition
            (string (Printf.sprintf "// register %s" (string_of_name id))
            ^^ hardline
            ^^ string (Printf.sprintf "%s %s%s;" (sgen_ctyp ctyp) (sgen_name id) (variable_zero_init ()))
            )
        in
        if Config.cpp then [definition]
        else
          [
            VariableDeclaration
              (string (Printf.sprintf "// register %s" (string_of_name id))
              ^^ hardline
              ^^ string (Printf.sprintf "extern %s %s;" (sgen_ctyp ctyp) (sgen_name id))
              );
            definition;
          ]
    | CDEF_val (id, _, arg_ctyps, ret_ctyp, extern) ->
        let external_name =
          match extern with
          | Some external_name -> Some external_name
          | None when ctx_is_extern id ctx -> Some (ctx_get_extern id ctx)
          | None -> None
        in
        let function_name = Option.value ~default:(sgen_function_id id) external_name in
        if Option.is_some external_name && not Config.optimized_model then []
        else if is_stack_ctyp ctx ret_ctyp then
          [
            FunctionDeclaration
              (string
                 (Printf.sprintf "%s %s(%s%s);" (sgen_ctyp ret_ctyp) function_name (extra_params ())
                    (Util.string_of_list ", " sgen_const_ctyp arg_ctyps)
                 )
              );
          ]
        else
          [
            FunctionDeclaration
              (string
                 (Printf.sprintf "void %s(%s%s *rop, %s);" function_name (extra_params ()) (sgen_ctyp ret_ctyp)
                    (Util.string_of_list ", " sgen_const_ctyp arg_ctyps)
                 )
              );
          ]
    | CDEF_fundef (id, ret_arg, args, instrs) ->
        (* We can skip the Sail version of a function if we're going to call the
          externally defined version anyway. *)
        if ctx_is_extern id ctx then []
        else (
          let _, arg_ctyps, ret_ctyp, _ =
            match Bindings.find_opt id ctx.valspecs with
            | Some vs -> vs
            | None -> c_error ~loc:(id_loc id) ("No valspec found for " ^ string_of_id id)
          in

          (* Check that the function has the correct arity at this point. *)
          if List.length arg_ctyps <> List.length args then
            c_error ~loc:(id_loc id)
              ("function arguments "
              ^ Util.string_of_list ", " string_of_name args
              ^ " matched against type "
              ^ Util.string_of_list ", " string_of_ctyp arg_ctyps
              )
          else ();

          let args =
            Util.string_of_list ", "
              (fun x -> x)
              (List.map2 (fun ctyp arg -> sgen_const_ctyp ctyp ^ " " ^ sgen_name arg) arg_ctyps args)
          in
          let function_header =
            match ret_arg with
            | Return_plain ->
                assert (is_stack_ctyp ctx ret_ctyp);
                string (sgen_ctyp ret_ctyp)
                ^^ space
                ^^ string (class_impl_prefix ())
                ^^ codegen_function_id id
                ^^ parens (string (extra_params ()) ^^ string args)
                ^^ hardline
            | Return_via gs ->
                assert (not (is_stack_ctyp ctx ret_ctyp));
                string "void" ^^ space
                ^^ string (class_impl_prefix ())
                ^^ codegen_function_id id
                ^^ parens
                     (string (extra_params ())
                     ^^ string (sgen_ctyp ret_ctyp ^ " *" ^ sgen_name gs ^ ", ")
                     ^^ string args
                     )
                ^^ hardline
          in
          [
            FunctionDefinition
              (function_header ^^ string "{"
              ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs)
              ^^ hardline ^^ string "}"
              );
          ]
        )
    | CDEF_type ctype_def -> codegen_type_def ctx ctype_def
    | CDEF_startup (id, instrs) ->
        let startup_header =
          string (Printf.sprintf "void %sstartup_%s(void)" (class_impl_prefix ()) (sgen_function_id id))
        in
        let startup_impl =
          separate_map hardline codegen_decl instrs
          ^^ twice hardline ^^ startup_header ^^ hardline ^^ string "{"
          ^^ jump 0 2 (separate_map hardline (codegen_alloc ctx) instrs)
          ^^ hardline ^^ string "}"
        in
        let startup_decl = string (Printf.sprintf "void startup_%s(void);" (sgen_function_id id)) in
        if Config.cpp then [FunctionDefinition startup_impl; FunctionDeclaration startup_decl]
        else [FunctionDefinition startup_impl]
    | CDEF_finish (id, instrs) ->
        let finish_header =
          string (Printf.sprintf "void %sfinish_%s(void)" (class_impl_prefix ()) (sgen_function_id id))
        in
        let finish_impl =
          separate_map hardline codegen_decl (List.filter is_decl instrs)
          ^^ twice hardline ^^ finish_header ^^ hardline ^^ string "{"
          ^^ jump 0 2 (separate_map hardline (codegen_instr id ctx) instrs)
          ^^ hardline ^^ string "}"
        in
        let finish_decl = string (Printf.sprintf "void finish_%s(void);" (sgen_function_id id)) in
        if Config.cpp then [FunctionDefinition finish_impl; FunctionDeclaration finish_decl]
        else [FunctionDefinition finish_impl]
    | CDEF_let (number, bindings, instrs) ->
        let setup = List.concat (List.map (fun (id, ctyp) -> [idecl (id_loc id) ctyp (name id)]) bindings) in
        let cleanup = List.concat (List.map (fun (id, ctyp) -> [iclear ~loc:(id_loc id) ctyp (name id)]) bindings) in
        let variable_defs =
          separate_map hardline
            (fun (id, ctyp) -> string (Printf.sprintf "%s %s%s;" (sgen_ctyp ctyp) (sgen_id id) (variable_zero_init ())))
            bindings
          ^^ hardline
        in
        let variable_decls =
          separate_map hardline
            (fun (id, ctyp) -> string (Printf.sprintf "extern %s %s;" (sgen_ctyp ctyp) (sgen_id id)))
            bindings
          ^^ hardline
        in
        let function_decls =
          string (Printf.sprintf "void create_letbind_%d(void);" number)
          ^^ hardline
          ^^ string (Printf.sprintf "void kill_letbind_%d(void);" number)
          ^^ hardline
        in
        let impl =
          string (Printf.sprintf "void %screate_letbind_%d(void) " (class_impl_prefix ()) number)
          ^^ string "{"
          ^^ jump 0 2 (separate_map hardline (codegen_alloc ctx) setup)
          ^^ hardline
          ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") { ctx with no_raw = true }) instrs)
          ^^ hardline ^^ string "}" ^^ hardline
          ^^ string (Printf.sprintf "void %skill_letbind_%d(void) " (class_impl_prefix ()) number)
          ^^ string "{"
          ^^ jump 0 2 (separate_map hardline (codegen_instr (mk_id "let") ctx) cleanup)
          ^^ hardline ^^ string "}"
        in

        (if Config.optimized_model then [VariableDeclaration variable_decls] else [])
        @ [VariableDefinition variable_defs; FunctionDeclaration function_decls; FunctionDefinition impl]
    | CDEF_pragma _ -> []

  (** As we generate C we need to generate specialized version of tuple, list, and vector type. These must be generated
      in the correct order. The ctyp_dependencies function generates a list of c_gen_typs in the order they must be
      generated. Types may be repeated in ctyp_dependencies so it's up to the code-generator not to repeat definitions
      pointlessly (using the !generated variable) *)
  type c_gen_typ =
    | CTG_native_int_conversion_failure
    | CTG_u128
    | CTG_u256
    | CTG_u320
    | CTG_fixed_bytes of int
    | CTG_tup of ctyp list
    | CTG_list of ctyp
    | CTG_vector of ctyp
    | CTG_fixed_vector of int * ctyp

  let rec ctyp_dependencies = function
    | CT_fint _ | CT_fuint _ -> [CTG_native_int_conversion_failure]
    | ctyp when is_c_repr_u128 ctyp -> [CTG_native_int_conversion_failure; CTG_u128]
    | ctyp when is_c_repr_u256 ctyp -> [CTG_native_int_conversion_failure; CTG_u256]
    | ctyp when is_c_repr_u320 ctyp -> [CTG_native_int_conversion_failure; CTG_u320]
    | ctyp when is_c_repr_fixed_bytes ctyp -> [CTG_fixed_bytes (Option.get (c_repr_fixed_bytes_length ctyp))]
    | CT_tup ctyps -> List.concat (List.map ctyp_dependencies ctyps) @ [CTG_tup ctyps]
    | CT_list ctyp -> ctyp_dependencies ctyp @ [CTG_list ctyp]
    | CT_vector ctyp -> ctyp_dependencies ctyp @ [CTG_vector ctyp]
    | CT_fvector (length, ctyp) -> ctyp_dependencies ctyp @ [CTG_fixed_vector (length, ctyp)]
    | CT_ref ctyp -> ctyp_dependencies ctyp
    | CT_struct (_, ctyps) | CT_variant (_, ctyps) -> List.concat (List.map ctyp_dependencies ctyps)
    | CT_lint | CT_lbits | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_real | CT_string | CT_enum _ | CT_poly _
    | CT_constant _ | CT_float _ | CT_rounding_mode | CT_memory_writes | CT_json | CT_json_key ->
        []

  (* Generate types and utility functions for non-bitvector vectors, tuples and lists.
     The functions are pure, and only emitted in the implementation file as static functions. *)
  let codegen_ctg ctx = function
    | CTG_native_int_conversion_failure -> codegen_native_int_conversion_failure ()
    | CTG_u128 -> codegen_u128 ()
    | CTG_u256 -> codegen_u256 ()
    | CTG_u320 -> codegen_u320 ()
    | CTG_fixed_bytes length -> codegen_fixed_bytes length
    | CTG_vector ctyp -> codegen_vector ctx ctyp
    | CTG_fixed_vector (length, ctyp) -> codegen_fixed_vector ctx length ctyp
    | CTG_tup ctyps -> codegen_tup ctx ctyps
    | CTG_list ctyp -> codegen_list ctx ctyp

  (* Take a single list of `Header doc`, `VariableDeclaration doc`, etc. and split them
     into separate lists each with only one type of `doc`. *)
  type file_docs_by_type = {
    type_decl : document;
    func_decl : document;
    func_def : document;
    var_decl : document;
    var_def : document;
    static_func_def : document;
  }

  let merge_file_docs docs =
    List.fold_left
      (fun acc -> function
        | TypeDeclaration doc -> { acc with type_decl = acc.type_decl ^^ doc ^^ twice hardline }
        | FunctionDeclaration doc -> { acc with func_decl = acc.func_decl ^^ doc ^^ twice hardline }
        | FunctionDefinition doc -> { acc with func_def = acc.func_def ^^ doc ^^ twice hardline }
        | VariableDeclaration doc -> { acc with var_decl = acc.var_decl ^^ doc ^^ twice hardline }
        | VariableDefinition doc -> { acc with var_def = acc.var_def ^^ doc ^^ twice hardline }
        | StaticFunctionDefinition doc -> { acc with static_func_def = acc.static_func_def ^^ doc ^^ twice hardline }
        )
      {
        type_decl = empty;
        func_decl = empty;
        func_def = empty;
        var_decl = empty;
        var_def = empty;
        static_func_def = empty;
      }
      docs

  (** When we generate code for a definition, we need to first generate any auxillary type definitions that are
      required. *)
  let codegen_def ctx def =
    match def with
    | CDEF_aux ((CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _)), _)
      when ctx_is_extern id ctx && not Config.optimized_model ->
        []
    | _ ->
        prepare_local_name_scope def;
        let ctyps = cdef_ctyps def |> CTSet.elements in
        (* We should have erased any polymorphism introduced by variants at this point! *)
        if List.exists is_polymorphic ctyps then (
          let polymorphic_ctyps = List.filter is_polymorphic ctyps in
          c_error
            (Printf.sprintf "Found polymorphic types:\n%s\nwhile generating definition."
               (Util.string_of_list "\n" string_of_ctyp polymorphic_ctyps)
            )
        )
        else (
          let deps = List.concat (List.map ctyp_dependencies ctyps) in
          List.concat (List.map (codegen_ctg ctx) deps) @ codegen_def' ctx def
        )

  let is_cdef_startup = function CDEF_aux (CDEF_startup _, _) -> true | _ -> false

  let sgen_startup = function
    | CDEF_aux (CDEF_startup (id, _), _) -> Printf.sprintf "  startup_%s();" (sgen_function_id id)
    | _ -> assert false

  let sgen_instr id ctx instr = Document.to_string (codegen_instr id ctx instr)

  let is_cdef_finish = function CDEF_aux (CDEF_startup _, _) -> true | _ -> false

  let sgen_finish = function
    | CDEF_aux (CDEF_startup (id, _), _) -> Printf.sprintf "  finish_%s();" (sgen_function_id id)
    | _ -> assert false

  let get_recursive_functions cdefs =
    let graph = Jib_compile.callgraph cdefs in
    let rf = IdGraph.self_loops graph in
    (* Use strongly-connected components for mutually recursive functions *)
    List.fold_left (fun rf component -> match component with [_] -> rf | mutual -> mutual @ rf) rf (IdGraph.scc graph)
    |> IdSet.of_list

  let jib_of_ast env effect_info ast =
    let module Jibc = Make (C_config (struct
      let branch_coverage = Config.branch_coverage
      let assert_to_exception = Config.assert_to_exception
      let preserve_types = Config.preserve_types
      let c_repr_unsigned = Config.c_repr_unsigned
      let c_repr_signed = Config.c_repr_signed
      let c_repr_u256 = Config.c_repr_u256
      let c_repr_fixed_bytes = Config.c_repr_fixed_bytes
      let specialize_c = Config.specialize_c
      let require_bounded_int = Config.require_bounded_int
      let optimized_model = Config.optimized_model
    end))
    in
    let ctx = initial_ctx env effect_info in
    Jibc.compile_ast ctx ast

  let rec c_ast_registers ~early = function
    | CDEF_aux (CDEF_register (id, ctyp, instrs), def_annot) :: ast
      when early = Option.is_some (get_def_attribute "early_init" def_annot) ->
        (id, ctyp, instrs) :: c_ast_registers ~early ast
    | _ :: ast -> c_ast_registers ~early ast
    | [] -> []

  let get_unit_tests cdefs =
    List.fold_left
      (fun ids -> function
        | CDEF_aux (CDEF_val (id, _, _, _, _), def_annot) when Option.is_some (get_def_attribute "test" def_annot) ->
            IdSet.add id ids
        | _ -> ids
        )
      IdSet.empty cdefs
    |> IdSet.elements

  (* Generate the `model_init()` and `model_fini()` functions
     which initialise and clean up the model (allocating/deallocating
     GMP variables, setting initial register values, etc.). *)
  let gen_model_init_fini ctx cdefs =
    let exception_type = sgen_id (mk_id "exception") in

    let exn_boilerplate =
      if not (Bindings.mem (mk_id "exception") ctx.variants) then ([], [])
      else
        ( [
            sprintf "  current_exception = sail_new(struct %s);" exception_type;
            sprintf "  CREATE(%s)(current_exception);" exception_type;
            "  throw_location = sail_new(sail_string);";
            "  CREATE(sail_string)(throw_location);";
          ],
          [
            "  if (have_exception) {fprintf(stderr, \"Exiting due to uncaught exception: %s\\n\", *throw_location);}";
            sprintf "  KILL(%s)(current_exception);" exception_type;
            "  sail_free(current_exception);";
            "  KILL(sail_string)(throw_location);";
            "  sail_free(throw_location);";
            "  if (have_exception) {exit(EXIT_FAILURE);}";
          ]
        )
    in

    let letbind_initializers = List.map (fun n -> Printf.sprintf "  create_letbind_%d();" n) (List.rev ctx.letbinds) in
    let letbind_finalizers = List.map (fun n -> Printf.sprintf "  kill_letbind_%d();" n) ctx.letbinds in

    let set_abstract_types =
      Bindings.bindings ctx.abstracts
      |> List.filter_map (fun (id, (_, initialised)) ->
          match initialised with
          | Initialised -> Some (Printf.sprintf "  sail_set_abstract_%s();" (Ast_util.string_of_id id))
          (* Skip abstract types that haven't been initialised; we can't initialise them automatically. *)
          | Uninitialised -> None
      )
    in

    let startup cdefs = List.map sgen_startup (List.filter is_cdef_startup cdefs) in
    let finish cdefs = List.map sgen_finish (List.filter is_cdef_finish cdefs) in

    let early_regs = c_ast_registers ~early:true cdefs in
    let regs = c_ast_registers ~early:false cdefs in

    let register_init_clear (id, ctyp, instrs) =
      if is_stack_ctyp ctx ctyp then (List.map (sgen_instr (mk_id "reg") ctx) instrs, [])
      else
        ( [Printf.sprintf "  CREATE(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name id)]
          @ List.map (sgen_instr (mk_id "reg") ctx) instrs,
          [Printf.sprintf "  KILL(%s)(&%s);" (sgen_ctyp_name ctyp) (sgen_name id)]
        )
    in

    let init_config_id = mk_id "__InitConfig" in

    let model_init_name = if Config.optimized_model then Config.package_name ^ "_model_init" else "model_init" in
    let model_init =
      separate hardline
        (List.map string
           ([Printf.sprintf "void %s%s(void)" (class_impl_prefix ()) model_init_name; "{"]
           @ (if Config.optimized_model then ["  have_exception = false;"] else ["  setup_rts();"] @ fst exn_boilerplate)
           @ List.concat (List.map (fun r -> fst (register_init_clear r)) early_regs)
           @ set_abstract_types @ startup cdefs @ letbind_initializers
           @ List.concat (List.map (fun r -> fst (register_init_clear r)) regs)
           @ (if regs = [] then [] else [Printf.sprintf "  %s(UNIT);" (sgen_function_id (mk_id "initialize_registers"))])
           @ ( if ctx_has_val_spec init_config_id ctx then
                 [Printf.sprintf "  %s(UNIT);" (sgen_function_id init_config_id)]
               else []
             )
           @ ["}"]
           )
        )
    in

    let model_fini =
      separate hardline
        (List.map string
           ([Printf.sprintf "void %smodel_fini(void)" (class_impl_prefix ()); "{"]
           @ List.concat (List.map (fun r -> snd (register_init_clear r)) regs)
           @ letbind_finalizers
           @ List.concat (List.map (fun r -> snd (register_init_clear r)) early_regs)
           @ finish cdefs @ ["  cleanup_rts();"] @ snd exn_boilerplate @ ["}"]
           )
        )
    in

    if Config.optimized_model then
      [FunctionDeclaration (Printf.ksprintf string "void %s(void);" model_init_name); FunctionDefinition model_init]
    else [FunctionDefinition model_init; FunctionDefinition model_fini]

  (* For C++ generate a constructor and destructor to allocate and free abstract
     types that aren't handled in model_init() and model_fini(). These
     cannot be initialised in model_init() because they must be set by
     sail_set_abstract_...() before model_init() runs. They aren't necessary
     in C because in C they are globals so they get automatically zero-initialised
     and Valgrind doesn't care about globals leaking. *)
  let gen_constructor_destructor ctx cdefs =
    let names_and_types =
      Bindings.bindings ctx.abstracts
      |> List.map (fun (id, (ctyp, _)) -> (NameGen.to_string ~prefix:"abstract_" () id, ctyp))
    in

    let create_abstract (name, ctyp) =
      if is_stack_ctyp ctx ctyp then empty else sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&%s" name
    in

    let kill_abstract (name, ctyp) =
      if is_stack_ctyp ctx ctyp then empty else sail_kill ~suffix:";" (sgen_ctyp_name ctyp) "&%s" name
    in

    let constructor_decl = ksprintf string "%s();" Config.cpp_class_name in
    let constructor_def =
      ksprintf string "%s::%s() {" Config.cpp_class_name Config.cpp_class_name
      ^^ jump 2 1 (separate_map hardline create_abstract names_and_types)
      ^^ string "}"
    in
    let destructor_decl = ksprintf string "~%s();" Config.cpp_class_name in
    let destructor_def =
      ksprintf string "%s::~%s() {" Config.cpp_class_name Config.cpp_class_name
      ^^ jump 2 1 (separate_map hardline kill_abstract names_and_types)
      ^^ string "}"
    in

    let copy_constructor_decl = ksprintf string "%s(const %s&) = delete;" Config.cpp_class_name Config.cpp_class_name in
    [
      FunctionDeclaration constructor_decl;
      FunctionDefinition constructor_def;
      FunctionDeclaration destructor_decl;
      FunctionDefinition destructor_def;
      FunctionDeclaration copy_constructor_decl;
    ]

  (* Generate a constant array that points to all the unit test functions. *)
  let gen_unit_test_defs ctx cdefs =
    let unit_tests = get_unit_tests cdefs in

    (* `static constexpr` is another option but it doesn't work for function pointers until C++20. *)
    let inline = if Config.cpp then "inline " else "" in

    [
      VariableDefinition
        ((* Number of unit tests. *)
         [sprintf "%sstatic const size_t SAIL_TEST_COUNT = %d;" inline (List.length unit_tests)]
         (* Pointers to unit test functions, with NULL entry for convenience. *)
         @ [
             sprintf "%sstatic unit (%s*const SAIL_TESTS[%d])(unit) = {" inline (class_impl_prefix ())
               (List.length unit_tests + 1);
           ]
         @ List.map (fun id -> sprintf "  &%s%s," (class_impl_prefix ()) (sgen_function_id id)) unit_tests
         @ ["  NULL"; "};"]
         (* Unit test names, with NULL entry for convenience. *)
         @ [sprintf "%sstatic const char* const SAIL_TEST_NAMES[%d] = {" inline (List.length unit_tests + 1)]
         @ List.map (fun id -> sprintf "  \"%s\"," (String.escaped (string_of_id id))) unit_tests
         @ ["  NULL"; "};"]
        |> List.map string |> separate hardline
        );
    ]

  let cdef_calls target cdef =
    let found = ref false in
    let inspect (I_aux (aux, _) as funcall) exception_instrs =
      (match aux with I_funcall (_, _, (callee, _), _) when Id.compare callee target = 0 -> found := true | _ -> ());
      funcall :: exception_instrs
    in
    ignore (cdef_map_funcall inspect cdef);
    !found

  let remove_uncalled_specialized_wrappers cdefs =
    let candidates = List.map mk_id ["neq_int"; "from_bytes_le"; "to_bytes_le"] in
    let uncalled = List.filter (fun candidate -> not (List.exists (cdef_calls candidate) cdefs)) candidates in
    let is_uncalled id = List.exists (fun candidate -> Id.compare candidate id = 0) uncalled in
    if Config.specialize_c then
      List.filter
        (function
          | CDEF_aux (CDEF_val (id, _, _, _, _), _)
          | CDEF_aux (CDEF_fundef (id, _, _, _), _)
          | CDEF_aux (CDEF_startup (id, _), _)
          | CDEF_aux (CDEF_finish (id, _), _)
            when is_uncalled id ->
              false
          | _ -> true
          )
        cdefs
    else cdefs

  let rec ctyp_contains pred ctyp =
    pred ctyp
    ||
    match ctyp with
    | CT_tup ctyps | CT_struct (_, ctyps) | CT_variant (_, ctyps) -> List.exists (ctyp_contains pred) ctyps
    | CT_fvector (_, ctyp) | CT_vector ctyp | CT_list ctyp | CT_ref ctyp -> ctyp_contains pred ctyp
    | _ -> false

  let cdefs_contain ctx pred cdefs =
    List.exists
      (function
        (* A polymorphic container definition necessarily uses placeholder
           representations for its type parameters.  Diagnose concrete
           instantiations and values, not the generic declaration itself. *)
        | CDEF_aux (CDEF_type (CTD_struct (_, params, _) | CTD_variant (_, params, _)), _)
          when not (Util.list_empty params) ->
            false
        (* A transparent alias is not storage by itself. Diagnose the concrete
           register, function, local, or aggregate that instantiates it. *)
        | CDEF_aux (CDEF_type (CTD_abbrev _), _) -> false
        (* Extern valspecs are retained in JIB for call typing, but codegen_def
           intentionally emits no declaration for them.  A real call still
           carries its argument/result types in an instruction and is counted. *)
        | CDEF_aux ((CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _)), _) when ctx_is_extern id ctx -> false
        | cdef -> cdef_has_ctyp (ctyp_contains pred) cdef
        )
      cdefs

  let self_dependent_assignments ast =
    let assignments = ref Util.StringSet.empty in
    let read_ids exp =
      let alg = { (Rewriter.pure_exp_alg IdSet.empty IdSet.union) with e_id = IdSet.singleton } in
      Rewriter.fold_exp alg exp
    in
    let rewrite_exp rewriters (E_aux (aux, _) as exp) =
      ( match aux with
      | E_assign (LE_aux (LE_id target, _), rhs) when IdSet.mem target (read_ids rhs) ->
          assignments := Util.StringSet.add (string_of_id target) !assignments
      | _ -> ()
      );
      Rewriter.rewrite_exp rewriters exp
    in
    let rewriters = { Rewriter.rewriters_base with rewrite_exp } in
    ignore (Rewriter.rewrite_ast_base rewriters ast);
    !assignments

  let compile_ast env effect_info basename ast =
    try
      let compile_started_at = Sys.time () in
      let log_phase format =
        Printf.ksprintf
          (fun message ->
            if !Jib_compile.opt_debug_function_representations then
              Printf.eprintf "C compilation: %s (%.2fs)\n%!" message (Sys.time () -. compile_started_at)
          )
          format
      in
      let self_dependent_assignments = self_dependent_assignments ast in
      log_phase "lowering Sail AST to JIB";
      let cdefs, ctx = jib_of_ast env effect_info ast in
      log_phase "lowered JIB definitions=%d" (List.length cdefs);
      (* let cdefs', _ = Jib_optimize.remove_tuples cdefs ctx in *)
      let cdefs = insert_heap_returns ctx Bindings.empty cdefs in

      let cdefs, fixed_bitvector_fusions =
        if Config.specialize_c then fuse_fixed_bitvector_webs cdefs else (cdefs, 0)
      in
      log_phase "fused fixed-bitvector webs=%d" fixed_bitvector_fusions;

      let recursive_functions = get_recursive_functions cdefs in
      log_phase "optimizing JIB definitions=%d recursive-functions=%d" (List.length cdefs)
        (IdSet.cardinal recursive_functions);
      let cdefs =
        optimize ~have_rts:(not Config.no_rts) ~specialize_c:Config.specialize_c ctx recursive_functions cdefs
      in
      log_phase "optimized JIB definitions=%d" (List.length cdefs);

      (* clang has a default limit of 256 nested braces, so we make
         sure we don't generated definitions with deep nesting by
         flattening all definitions with a nesting depth greater than
         some value < 256 (100 seems reasonable). *)
      let cdefs = List.map (Jib_optimize.flatten_cdef ~max_depth:100) cdefs in

      (* Native comparisons replace every represented call to neq_int, but its
         generic library wrapper otherwise survives as an unused public C
         function.  Drop that wrapper only after proving there are no JIB
         calls left, then use the final program to decide whether compatibility
         helpers for generic runtime values are needed at all. *)
      let cdefs = remove_uncalled_specialized_wrappers cdefs in
      let has_sail_int = cdefs_contain ctx (function CT_lint -> true | _ -> false) cdefs in
      let has_lbits = cdefs_contain ctx (function CT_lbits -> true | _ -> false) cdefs in
      let has_sail_config = cdefs_contain ctx (function CT_json | CT_json_key -> true | _ -> false) cdefs in
      let is_managed_ctyp = function
        | CT_lint | CT_lbits | CT_real | CT_string | CT_list _ | CT_vector _ | CT_memory_writes | CT_json
        | CT_json_key | CT_ref _ ->
            true
        | _ -> false
      in
      let has_managed_representation =
        cdefs_contain ctx is_managed_ctyp cdefs
      in
      let managed_ctyp_names cdef =
        let names = ref Util.StringSet.empty in
        let collect =
          object
            inherit empty_jib_visitor

            method! vctyp ctyp =
              if is_managed_ctyp ctyp then names := Util.StringSet.add (string_of_ctyp ctyp) !names;
              DoChildren
          end
        in
        ignore (visit_cdefs collect [cdef]);
        Util.StringSet.elements !names
      in
      if Config.require_bounded_int && has_sail_int then (
        let owner, loc, lifecycle_hint =
          List.find_map
            (fun (CDEF_aux (cdef, def_annot) as annotated) ->
              let omitted_extern =
                match cdef with
                | CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _) -> ctx_is_extern id ctx
                | _ -> false
              in
              let polymorphic_container =
                match cdef with
                | CDEF_type (CTD_struct (_, params, _) | CTD_variant (_, params, _)) -> not (Util.list_empty params)
                | _ -> false
              in
              let transparent_alias = match cdef with CDEF_type (CTD_abbrev _) -> true | _ -> false in
              if
                (not omitted_extern) && (not polymorphic_container) && (not transparent_alias)
                && cdef_has_ctyp (ctyp_contains (function CT_lint -> true | _ -> false)) annotated
              then (
                if !Jib_compile.opt_debug_function_representations then (
                  match cdef with
                  | CDEF_let (_, bindings, instrs) ->
                      Printf.eprintf "C representation specialization: unresolved top-level let [%s]\n%!"
                        (Util.string_of_list ", "
                           (fun (id, ctyp) -> string_of_id id ^ " : " ^ string_of_ctyp ctyp)
                           bindings
                        );
                      List.iter (fun instr -> Printf.eprintf "  %s\n%!" (string_of_instr instr)) instrs
                  | CDEF_fundef (id, _, params, instrs) ->
                      Printf.eprintf "C representation specialization: unresolved function %s params=[%s]\n%!"
                        (string_of_id id)
                        (Util.string_of_list ", " (fun param -> string_of_name ~zencode:false param) params);
                      List.iter (fun instr -> Printf.eprintf "  %s\n%!" (string_of_instr instr)) instrs
                  | _ -> ()
                );
                let owner =
                  match cdef with
                  | CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _) | CDEF_startup (id, _) | CDEF_finish (id, _)
                    ->
                      "definition " ^ string_of_id id
                  | CDEF_register (name, _, _) -> "register " ^ string_of_name ~zencode:false name
                  | CDEF_let (index, bindings, _) ->
                      let names = Util.string_of_list ", " (fun (id, _) -> string_of_id id) bindings in
                      if names = "" then "top-level let " ^ string_of_int index else "top-level let " ^ names
                  | CDEF_type ctyp_def -> "type definition " ^ string_of_id (ctype_def_id ctyp_def)
                  | CDEF_pragma (name, _) -> "pragma " ^ name
                in
                let lifecycle_hint =
                  match cdef with
                  | CDEF_register (name, _, _)
                    when Util.StringSet.mem (string_of_name ~zencode:false name) self_dependent_assignments ->
                      Some
                        " This register has a self-dependent accumulator update, so two independently bounded operands \
                         do not prove that the sum remains in range; use a finite signed range and narrow the sum at \
                         the semantic update boundary."
                  | _ -> None
                in
                Some (owner, def_annot.loc, lifecycle_hint)
              )
              else None
            )
            cdefs
          |> Option.value ~default:("the generated model", Parse_ast.Unknown, None)
        in
        raise
          (Reporting.err_general loc
             (Printf.sprintf
                "C backend: cannot select a native integer representation for %s; add a finite semantic bound to the \
                 corresponding Sail type, parameter, result, local value, or container element.%s (Omit \
                 --c-require-bounded-int when arbitrary precision is intentional.)"
                owner
                (Option.value ~default:"" lifecycle_hint)
             )
          )
      );
      if Config.optimized_model && has_managed_representation then (
        let owner, loc, managed_types =
          List.find_map
            (fun (CDEF_aux (cdef, def_annot) as annotated) ->
              let ignored =
                match cdef with
                | CDEF_type (CTD_struct (_, params, _) | CTD_variant (_, params, _)) ->
                    not (Util.list_empty params)
                | CDEF_type (CTD_abbrev _) -> true
                | CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _) -> ctx_is_extern id ctx
                | _ -> false
              in
              if (not ignored) && cdef_has_ctyp (ctyp_contains is_managed_ctyp) annotated then
                let owner =
                  match cdef with
                  | CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _) | CDEF_startup (id, _)
                  | CDEF_finish (id, _) ->
                      "definition " ^ string_of_id id
                  | CDEF_register (name, _, _) -> "register " ^ string_of_name ~zencode:false name
                  | CDEF_let (index, bindings, _) ->
                      let names = Util.string_of_list ", " (fun (id, _) -> string_of_id id) bindings in
                      if names = "" then "top-level let " ^ string_of_int index else "top-level let " ^ names
                  | CDEF_type ctyp_def -> "type definition " ^ string_of_id (ctype_def_id ctyp_def)
                  | CDEF_pragma (name, _) -> "pragma " ^ name
                in
                Some (owner, def_annot.loc, managed_ctyp_names annotated)
              else None
            )
            cdefs
          |> Option.value ~default:("the generated model", Parse_ast.Unknown, [])
        in
        raise
          (Reporting.err_general loc
             (Printf.sprintf
                "C backend: --c-optimized-model requires every generated value to have a fixed, unmanaged C \n\
                 representation, but %s still contains an unbounded integer, dynamic bitvector/container, string, \n\
                 real, JSON value, memory-write log, or reference after specialization.%s"
                owner
                (match managed_types with
                | [] -> ""
                | types -> " Managed JIB representation(s): " ^ String.concat ", " types ^ "."
                )
             )
          )
      );
      emit_generic_sail_int_helpers := (not Config.specialize_c) || has_sail_int;
      emit_generic_lbits_helpers := (not Config.specialize_c) || has_lbits;

      generated := IdSet.empty;
      emitted_external_functions := Util.StringSet.empty;
      readable_ctyp_names := CTMap.empty;
      readable_ctyp_names_used := Util.StringSet.empty;
      if Config.no_mangle then (
        let reserve_nominal_types =
          object
            inherit empty_jib_visitor

            method! vctyp ctyp =
              ( match ctyp with
              | CT_struct (id, _) | CT_variant (id, _) | CT_enum id ->
                  readable_ctyp_names_used := Util.StringSet.add (sgen_id id) !readable_ctyp_names_used
              | _ -> ()
              );
              DoChildren
          end
        in
        ignore (visit_cdefs reserve_nominal_types cdefs)
      );

      (* Modular C emission must choose an owner before auxiliary carrier
         types are generated.  Otherwise the global [generated] set attaches
         a fixed vector/tuple/byte carrier to whichever definition happens to
         be visited first, which need not be the earliest module that uses it.
         Compute effective ownership from the complete nominal type graph,
         then visit definitions in stable module order. *)
      let modular_layout =
        match !requested_modules with
        | None -> None
        | Some (_, requested) ->
            let modules = Array.of_list requested in
            let rec filename_of_loc = function
              | Parse_ast.Unknown -> None
              | Parse_ast.Unique (_, loc) | Parse_ast.Generated loc -> filename_of_loc loc
              | Parse_ast.Hint (_, loc, _) -> filename_of_loc loc
              | Parse_ast.Range (start_pos, _) -> Some start_pos.Lexing.pos_fname
            in
            let same_file left right =
              String.equal left right || String.equal (Filename.basename left) (Filename.basename right)
            in
            let module_index_of_loc loc =
              match filename_of_loc loc with
              | None -> 0
              | Some filename ->
                  let rec find index =
                    if index = Array.length modules then 0
                    else if List.exists (same_file filename) modules.(index).files then index
                    else find (index + 1)
                  in
                  find 0
            in
            let type_owners = ref Bindings.empty in
            let type_definitions =
              List.filter_map
                (function
                  | CDEF_aux (CDEF_type ctype_def, def_annot) -> Some (ctype_def, def_annot)
                  | _ -> None
                )
                cdefs
            in
            List.iter
              (fun (ctype_def, (def_annot : unit def_annot)) ->
                type_owners :=
                  Bindings.add (ctype_def_id ctype_def) (module_index_of_loc def_annot.loc) !type_owners
              )
              type_definitions;
            let type_dependencies ctype_def =
              let contained_ctyps =
                match ctype_def with
                | CTD_enum _ | CTD_abstract _ -> []
                | CTD_abbrev (_, ctyp) -> [ctyp]
                | CTD_struct (_, _, fields) | CTD_variant (_, _, fields) -> List.map snd fields
              in
              List.fold_left
                (fun ids ctyp -> IdSet.union ids (ctyp_ids ctyp))
                IdSet.empty contained_ctyps
            in
            let changed = ref true in
            while !changed do
              changed := false;
              List.iter
                (fun (ctype_def, _) ->
                  let id = ctype_def_id ctype_def in
                  let current = Option.value ~default:0 (Bindings.find_opt id !type_owners) in
                  let required =
                    IdSet.fold
                      (fun dependency owner ->
                        max owner (Option.value ~default:0 (Bindings.find_opt dependency !type_owners))
                      )
                      (type_dependencies ctype_def) current
                  in
                  if required <> current then (
                    type_owners := Bindings.add id required !type_owners;
                    changed := true
                  )
                )
                type_definitions
            done;
            let dependency_owner ctyp owner =
              IdSet.fold
                (fun dependency owner ->
                  max owner (Option.value ~default:0 (Bindings.find_opt dependency !type_owners))
                )
                (ctyp_ids ctyp) owner
            in
            let module_index (CDEF_aux (cdef, def_annot) as annotated) =
              let source_owner = module_index_of_loc def_annot.loc in
              let nominal_owner =
                match cdef with
                | CDEF_type ctype_def ->
                    Option.value ~default:source_owner (Bindings.find_opt (ctype_def_id ctype_def) !type_owners)
                | _ -> source_owner
              in
              CTSet.fold dependency_owner (cdef_ctyps annotated) nominal_owner
            in
            Some (modules, module_index)
      in
      let cdefs =
        match modular_layout with
        | None -> cdefs
        | Some (_, module_index) ->
            List.stable_sort (fun left right -> Int.compare (module_index left) (module_index right)) cdefs
      in

      log_phase "generating C definitions=%d" (List.length cdefs);
      let docs_by_definition = List.map (fun cdef -> (cdef, codegen_def ctx cdef)) cdefs in
      let docs_by_definition =
        if Config.optimized_model then
          List.map
            (fun ((CDEF_aux (cdef, _) as annotated), docs) ->
              match cdef with
              | CDEF_val (id, _, _, _, extern) when Option.is_some extern || ctx_is_extern id ctx ->
                  let function_name = match extern with Some name -> name | None -> ctx_get_extern id ctx in
                  if Util.StringSet.mem function_name !emitted_external_functions then (annotated, docs)
                  else (annotated, [])
              | CDEF_val _ -> (annotated, docs)
              | _ -> (annotated, docs)
            )
            docs_by_definition
        else docs_by_definition
      in
      let definition_docs = List.concat (List.map snd docs_by_definition) in
      let model_docs = gen_model_init_fini ctx cdefs in
      let unit_test_docs = if Config.optimized_model then [] else gen_unit_test_defs ctx cdefs in
      let docs = definition_docs @ model_docs @ unit_test_docs in
      let docs = if Config.cpp then docs @ gen_constructor_destructor ctx cdefs else docs in

      let docs_by_type = docs |> merge_file_docs in

      let extern_cpp_begin =
        if Config.cpp then [] else [string "#ifdef __cplusplus"; string "extern \"C\" {"; string "#endif"]
      in
      let extern_cpp_end =
        if Config.cpp then [] else [string ""; string "#ifdef __cplusplus"; string "}"; string "#endif"]
      in

      let coverage_include, coverage_hook_header, coverage_hook =
        let header = string "#include \"sail_coverage.h\"" in
        (* Generate a hook for the RTS to call if we have coverage
           enabled, so it can set the output file with an option. *)
        let coverage_hook_header = string "extern void (*sail_rts_set_coverage_file)(const char *);" in
        let coverage_hook = string "void (*sail_rts_set_coverage_file)(const char *) = &sail_set_coverage_file;" in
        let no_coverage_hook = string "void (*sail_rts_set_coverage_file)(const char *) = NULL;" in
        match Config.branch_coverage with
        | Some _ -> if Config.no_rts then ([header], [], []) else ([header], [coverage_hook_header], [coverage_hook])
        | None -> if Config.no_rts then ([], [], []) else ([], [coverage_hook_header], [no_coverage_hook])
      in

      let preamble in_header =
        separate hardline
          (( if Config.optimized_model then
               [
                 string "#include <stdbool.h>";
                 string "#include <stddef.h>";
                 string "#include <stdint.h>";
                 string "#include <stdio.h>";
                 string "#include <stdlib.h>";
                 string "#include <string.h>";
                 string "#ifndef SAIL_FIXED_ABI_BASE_DEFINED";
                 string "#define SAIL_FIXED_ABI_BASE_DEFINED";
                 string "typedef uint64_t unit;";
                 string "#define UNIT UINT64_C(0)";
                 string "#define EQUAL(type) eq_ ## type";
                 string "#define UNDEFINED(type) undefined_ ## type";
                 string "static inline bool eq_unit(unit lhs, unit rhs) { return lhs == rhs; }";
                 string "static inline bool eq_bool(bool lhs, bool rhs) { return lhs == rhs; }";
                 string "static inline bool eq_fbits(uint64_t lhs, uint64_t rhs) { return lhs == rhs; }";
                 string "static inline unit undefined_unit(unit value) { return value; }";
                 string "static inline bool undefined_bool(unit unused) { (void)unused; return false; }";
                 string "static inline uint64_t undefined_fbits(unit unused) { (void)unused; return UINT64_C(0); }";
                 string
                   "static inline uint64_t safe_rshift(uint64_t value, uint64_t amount) { return amount >= UINT64_C(64) ? UINT64_C(0) : value >> amount; }";
                 string
                   "static inline void sail_match_failure(const char *function) { fprintf(stderr, \"Sail match failure in %s\\n\", function); abort(); }";
                 string "#endif";
               ]
             else if Config.no_lib then []
             else
               [string "#include \"sail.h\""]
               @ (if has_sail_config then [string "#include \"sail_config.h\""] else [])
               @ [string "#include <string.h>"]
           )
          @ (if Config.no_rts then [] else [string "#include \"rts.h\""; string "#include \"elf.h\""])
          @ coverage_include
          @ List.map
              (fun h -> string (Printf.sprintf "#include \"%s\"" h))
              (if in_header then Config.header_includes else Config.includes)
          @ extern_cpp_begin
          @ if in_header then coverage_hook_header else coverage_hook
          )
      in

      (* model_pre_exit() has to be `extern "C"` because it is called from rts.c. *)
      let extern_c = if Config.cpp then "extern \"C\" " else "" in

      let model_pre_exit =
        ([sprintf "%svoid model_pre_exit()" extern_c; "{"]
        @
        if Option.is_some Config.branch_coverage then
          [
            "  if (sail_coverage_exit() != 0) {";
            "    fprintf(stderr, \"Could not write coverage information\\n\");";
            "    exit(EXIT_FAILURE);";
            "  }";
            "}";
          ]
        else ["}"]
        )
        |> List.map string |> separate hardline
      in

      let model_main =
        ( if Config.cpp then
            [
              "int model_main(int argc, char *argv[])";
              "{";
              Printf.sprintf "  %s::%s model;" Config.cpp_namespace Config.cpp_class_name;
              "  model.model_init();";
              "  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);";
              Printf.sprintf "  model.%s(UNIT);" (sgen_function_id (mk_id "main"));
              "  model.model_fini();";
              "  model_pre_exit();";
              "  return EXIT_SUCCESS;";
              "}";
            ]
          else
            [
              "int model_main(int argc, char *argv[])";
              "{";
              "  model_init();";
              "  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);";
              Printf.sprintf "  %s(UNIT);" (sgen_function_id (mk_id "main"));
              "  model_fini();";
              "  model_pre_exit();";
              "  return EXIT_SUCCESS;";
              "}";
            ]
        )
        |> List.map string |> separate hardline
      in

      (* A simple function to run the unit tests. It isn't called from anywhere
         by default and you don't need to use it - you can use SAIL_TESTS directly
         in your own custom test runner. *)
      let model_test =
        if Config.optimized_model then empty
        else
        ( if Config.cpp then
            [
              "void model_test(void)";
              "{";
              sprintf "  %s::%s model;" Config.cpp_namespace Config.cpp_class_name;
              sprintf "  for (size_t i = 0; i < %s::%s::SAIL_TEST_COUNT; ++i) {" Config.cpp_namespace
                Config.cpp_class_name;
              "    model.model_init();";
              sprintf "    printf(\"Testing %%s\\n\", %s::%s::SAIL_TEST_NAMES[i]);" Config.cpp_namespace
                Config.cpp_class_name;
              sprintf "    (model.*%s::%s::SAIL_TESTS[i])(UNIT);" Config.cpp_namespace Config.cpp_class_name;
              "    printf(\"Pass\\n\");";
              "    model.model_fini();";
              "  }";
              "}";
            ]
          else
            [
              "void model_test(void)";
              "{";
              "  for (size_t i = 0; i < SAIL_TEST_COUNT; ++i) {";
              "    model_init();";
              "    printf(\"Testing %s\\n\", SAIL_TEST_NAMES[i]);";
              "    SAIL_TESTS[i](UNIT);";
              "    printf(\"Pass\\n\");";
              "    model_fini();";
              "  }";
              "}";
            ]
        )
        |> List.map string |> separate hardline
      in

      let actual_main =
        let extra_pre =
          List.filter_map
            (function CDEF_aux (CDEF_pragma ("c_in_main", arg), _) -> Some ("  " ^ arg) | _ -> None)
            cdefs
        in
        let extra_post =
          List.filter_map
            (function CDEF_aux (CDEF_pragma ("c_in_main_post", arg), _) -> Some ("  " ^ arg) | _ -> None)
            cdefs
        in
        separate hardline
          ( if Config.no_main then []
            else
              List.map string
                (["int main(int argc, char *argv[])"; "{"; "  int retcode;"]
                @ extra_pre @ ["  retcode = model_main(argc, argv);"] @ extra_post @ ["  return retcode;"; "}"]
                )
          )
      in

      let hlhl = twice hardline in

      (* If compiling in C++ mode wrap the header in a struct { }. *)
      let header_doc =
        if Config.cpp then (
          let derive_from = match Config.cpp_derive_from with Some s -> " : " ^ s | None -> "" in
          ksprintf string "namespace %s {" Config.cpp_namespace
          ^^ hardline ^^ docs_by_type.type_decl
          ^^ ksprintf string "class %s%s {" Config.cpp_class_name derive_from
          ^^ hardline ^^ string "public:" ^^ hardline
          (* All of the types, functions and register declarations. *)
          ^^ jump 2 1
               (docs_by_type.func_decl ^^ docs_by_type.var_def ^^ string "void model_init();" ^^ hardline
              ^^ string "void model_fini();" ^^ hardline
               )
          (* End of struct *)
          ^^ string "};"
          ^^ hardline ^^ string "} // namespace" ^^ hardline
        )
        else docs_by_type.type_decl ^^ docs_by_type.func_decl ^^ docs_by_type.var_decl
      in

      let header =
        string "#pragma once" ^^ hlhl ^^ preamble true ^^ hlhl ^^ header_doc ^^ hardline
        ^^ separate hardline extern_cpp_end ^^ hardline
        |> Document.to_string
      in

      let impl_doc =
        if Config.cpp then
          ksprintf string "namespace %s {" Config.cpp_namespace
          ^^ hlhl ^^ docs_by_type.static_func_def ^^ docs_by_type.func_def
          ^^ ksprintf string "} // namespace %s" Config.cpp_namespace
          ^^ hardline
        else docs_by_type.static_func_def ^^ docs_by_type.var_def ^^ docs_by_type.func_def
      in

      let impl =
        Document.to_string
          (preamble false ^^ hardline
          ^^ Printf.ksprintf string "#include \"%s.h\"" basename
          ^^ hlhl ^^ impl_doc ^^ hlhl
          (* TODO: Does no_rts actually work? Won't actual_main try to call model_main which is missing? *)
          ^^ (if not Config.no_rts then model_pre_exit ^^ hlhl ^^ model_main ^^ hlhl else empty)
          ^^ model_test ^^ hlhl ^^ actual_main ^^ hardline ^^ separate hardline extern_cpp_end ^^ hardline
          )
      in

      ( match !requested_modules with
      | None -> ()
      | Some (package, _) ->
          let modules, module_index = Option.get modular_layout in
          let module_docs = Array.make (Array.length modules) [] in
          List.iter
            (fun (annotated, docs) ->
              let index = module_index annotated in
              module_docs.(index) <- List.rev_append docs module_docs.(index)
            )
            docs_by_definition;
          Array.iteri (fun index docs -> module_docs.(index) <- List.rev docs) module_docs;
          if Array.length modules > 0 then
            module_docs.(Array.length modules - 1) <- module_docs.(Array.length modules - 1) @ model_docs @ unit_test_docs;
          let all_static = (merge_file_docs docs).static_func_def in
          let include_module stem = ksprintf string "#include \"%s/spec/%s.h\"" package stem in
          let find_required name =
            Array.to_list modules
            |> List.find_opt (fun (mdl : c_module) -> String.equal mdl.name name)
          in
          let output_for index (mdl : c_module) =
            let split = merge_file_docs module_docs.(index) in
            let required_headers =
              List.filter_map
                (fun name ->
                  Option.map (fun (required : c_module) -> include_module required.file_stem) (find_required name)
                )
                mdl.requires
            in
            let header_doc =
              string "#pragma once" ^^ twice hardline
              ^^ separate hardline required_headers
              ^^ (if required_headers = [] then empty else twice hardline)
              ^^ preamble true ^^ twice hardline
              ^^ split.type_decl ^^ split.func_decl ^^ split.var_decl
              ^^ separate hardline extern_cpp_end ^^ hardline
            in
            let implementation_doc =
              ksprintf string "#include \"%s/spec.h\"" package
              ^^ twice hardline ^^ all_static ^^ split.var_def ^^ split.func_def
            in
            {
              name = mdl.name;
              file_stem = mdl.file_stem;
              header = Document.to_string header_doc;
              implementation = Document.to_string implementation_doc;
            }
          in
          generated_modules := Some (Array.to_list (Array.mapi output_for modules))
      );

      log_phase "complete header-bytes=%d implementation-bytes=%d" (String.length header) (String.length impl);
      (header, impl)
    with Type_error.Type_error (l, err) ->
      c_error ~loc:l ("Unexpected type error when compiling to C:\n" ^ fst (Type_error.string_of_type_error err))

  let compile_ast_modules env effect_info ~package (modules : c_module list) ast =
    if modules = [] then c_error "--c-optimized-model requires a Sail project containing at least one module";
    requested_modules := Some (package, modules);
    generated_modules := None;
    let _, _ =
      Fun.protect
        ~finally:(fun () -> requested_modules := None)
        (fun () -> compile_ast env effect_info package ast)
    in
    match !generated_modules with
    | Some outputs ->
        let umbrella =
          "#pragma once\n\n"
          ^ String.concat "\n"
              (List.map
                 (fun output -> Printf.sprintf "#include \"%s/spec/%s.h\"" package output.file_stem)
                 outputs
              )
          ^ "\n"
        in
        (umbrella, outputs)
    | None -> c_error "failed to produce modular optimized-model output"
end
