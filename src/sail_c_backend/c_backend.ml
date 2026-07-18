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

(* C-only opaque JIB markers for representations that have no general-purpose
   JIB equivalent.  Encoding them as reserved synthetic structs keeps the
   representation choice local to the C backend: the Sail and proof backends
   continue to see bits(256) and vector(N, byte), while C gets POD value types. *)
let c_repr_u256_id = mk_id "__sail_c_repr_u256"
let c_repr_fixed_bytes_id = mk_id "__sail_c_repr_fixed_bytes"
let c_repr_u256_ctyp = CT_struct (c_repr_u256_id, [])
let c_repr_fixed_bytes_ctyp n = CT_struct (c_repr_fixed_bytes_id, [CT_constant (Big_int.of_int n)])

let is_c_repr_u256 = function
  | CT_struct (id, []) -> Id.compare id c_repr_u256_id = 0
  | _ -> false

let c_repr_fixed_bytes_length = function
  | CT_struct (id, [CT_constant n]) when Id.compare id c_repr_fixed_bytes_id = 0 -> (
      try Some (Big_int.to_int n) with _ -> None
    )
  | _ -> None

let is_c_repr_fixed_bytes ctyp = Option.is_some (c_repr_fixed_bytes_length ctyp)
let is_c_repr_value ctyp = is_c_repr_u256 ctyp || is_c_repr_fixed_bytes ctyp

let rec ctyp_suprema_for_c specialize = function
  | ctyp when specialize && is_c_repr_value ctyp -> ctyp
  | (CT_fint _ | CT_fuint _ | CT_fbits _ | CT_sbits _) as ctyp when specialize -> ctyp
  | CT_tup ctyps when specialize -> CT_tup (List.map (ctyp_suprema_for_c specialize) ctyps)
  | CT_vector ctyp when specialize -> CT_vector (ctyp_suprema_for_c specialize ctyp)
  | CT_fvector (_, ctyp) when specialize -> CT_vector (ctyp_suprema_for_c specialize ctyp)
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
  | CT_fint n | CT_fuint n -> n <= 64
  | CT_lint when !optimize_fixed_int -> true
  | CT_lint -> false
  | CT_lbits when !optimize_fixed_bits -> true
  | CT_lbits -> false
  | CT_real | CT_string | CT_list _ | CT_vector _ | CT_fvector _ -> false
  | CT_struct (_, _) ->
      let _, fields = struct_field_bindings Parse_ast.Unknown ctx ctyp in
      Bindings.for_all (fun _ ctyp -> is_stack_ctyp ctx ctyp) fields
  | CT_variant (_, _) -> false
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
  val c_repr_uint64 : IdSet.t
  val c_repr_int64 : IdSet.t
  val c_repr_u256 : IdSet.t
  val c_repr_fixed_bytes : int Bindings.t
  val specialize_c : bool
end) : CONFIG = struct
  (* Representation annotations are C-only and may sit behind one or more
     transparent Sail aliases. Inspect that chain before expand_synonyms erases
     the semantic type names. *)
  let rec has_c_repr_uint64 env (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_id id when IdSet.mem id Opts.c_repr_uint64 -> true
    | Typ_id id -> (
        match Bindings.find_opt id (Env.get_typ_synonyms env) with
        | Some ([], A_aux (A_typ typ, _)) -> has_c_repr_uint64 env typ
        | _ -> false
      )
    | _ -> false

  let rec has_c_repr_int64 env (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_id id when IdSet.mem id Opts.c_repr_int64 -> true
    | Typ_id id -> (
        match Bindings.find_opt id (Env.get_typ_synonyms env) with
        | Some ([], A_aux (A_typ typ, _)) -> has_c_repr_int64 env typ
        | _ -> false
      )
    | _ -> false

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
    if Opts.specialize_c && IdSet.mem id Opts.c_repr_uint64 then CT_fuint 64
    else if Opts.specialize_c && IdSet.mem id Opts.c_repr_int64 then CT_fint 64
    else if Opts.specialize_c && IdSet.mem id Opts.c_repr_u256 then c_repr_u256_ctyp
    else
      match Bindings.find_opt id Opts.c_repr_fixed_bytes with
      | Some length when Opts.specialize_c -> c_repr_fixed_bytes_ctyp length
      | _ -> ctyp

  let representation_refines ~semantic ~represented =
    match (semantic, represented) with
    | CT_lint, (CT_fint _ | CT_fuint _) -> true
    | CT_lbits, represented when is_c_repr_u256 represented -> true
    | (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented
      when is_c_repr_fixed_bytes represented ->
        true
    | _ -> false

  (* Flow typing can refine a local integer to a range whose preferred native
     signedness differs from the C type selected when the storage was
     declared.  The important representation for an occurrence of that local
     is its actual storage type: both CT_fint and CT_fuint are stack values,
     and changing flow facts must not make the optimizer pretend the value is
     heap-backed.  This is intentionally local-storage compatibility rather
     than a general representation refinement rule. *)
  let fixed_integer_storage_compatible ~semantic ~represented =
    match (semantic, represented) with
    | (CT_fint semantic_width | CT_fuint semantic_width),
      (CT_fint represented_width | CT_fuint represented_width) ->
        semantic_width = represented_width
    | _ -> false

  let preserve_aval_representation ~semantic ~represented =
    match semantic with
    | CT_lint -> (
        match represented with CT_fint _ | CT_fuint _ -> true | _ -> false
      )
    | CT_lbits -> is_c_repr_u256 represented
    | CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8) -> is_c_repr_fixed_bytes represented
    | _ -> false

  let propagate_newtype_payload_representation id ~semantic:_ ~represented =
    (IdSet.mem id Opts.c_repr_uint64 && ctyp_equal represented (CT_fuint 64))
    || (IdSet.mem id Opts.c_repr_int64 && ctyp_equal represented (CT_fint 64))
    || (IdSet.mem id Opts.c_repr_u256 && is_c_repr_u256 represented)
    ||
    match Bindings.find_opt id Opts.c_repr_fixed_bytes with
    | Some length when Opts.specialize_c -> ctyp_equal represented (c_repr_fixed_bytes_ctyp length)
    | _ -> false

  let specialize_call_result id arg_ctyps semantic =
    let preserves_first_argument =
      match string_of_id id with
      | "vector_update" | "vector_update_inc" | "internal_vector_update"
      | "add_bits" | "sub_bits" | "not_bits" | "and_bits" | "or_bits" | "xor_bits"
      | "mult_vec" | "mults_vec" | "shiftl" | "shiftr" | "arith_shiftr" ->
          true
      | _ -> false
    in
    match (preserves_first_argument, arg_ctyps) with
    | true, represented :: _ when representation_refines ~semantic ~represented -> represented
    | _ -> semantic

  let specialize_call_destination ctx id arg_ctyps ~semantic ~represented =
    let external_name = if ctx_is_extern id ctx then ctx_get_extern id ctx else string_of_id id in
    let specialized = specialize_call_result (mk_id external_name) arg_ctyps semantic in
    if ctyp_equal specialized represented then true
    else
      match (external_name, semantic, represented, arg_ctyps) with
      | ("zero_extend" | "sail_zero_extend"), CT_lbits, represented, (CT_fbits _ | CT_lbits) :: _
        when is_c_repr_u256 represented ->
          true
      | "vector_init", (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented, _
        when is_c_repr_fixed_bytes represented ->
          true
      | _ -> false

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
      match arg_ctyps with
      | [left; right] -> is_c_repr_fixed_bytes left && ctyp_equal left right
      | _ -> false
    in
    match (external_name, return_ctyp, index, semantic, represented) with
    | "eq_anything", CT_bool, (0 | 1),
      (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented
      when arguments_share_fixed_bytes && is_c_repr_fixed_bytes represented ->
        true
    | ("vector_access" | "vector_access_inc" | "fast_vector_access"), _, 0,
      (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented
      when is_c_repr_fixed_bytes represented ->
        true
    | ("vector_access" | "vector_access_inc" | "fast_vector_access"), _, 0, CT_lbits, represented
      when is_c_repr_u256 represented ->
        true
    | ("vector_access" | "vector_access_inc" | "fast_vector_access" | "fast_unsigned_vector_access"), _, 1,
      CT_lint,
      (CT_fint _ | CT_fuint _)
      when first_argument_is_fixed_bytes || first_argument_is_vector ->
        true
    | "vector_init", return_ctyp, 0, CT_lint, (CT_fint _ | CT_fuint _)
      when is_c_repr_fixed_bytes return_ctyp
           || (match return_ctyp with CT_vector _ | CT_fvector _ -> true | _ -> false) ->
        true
    | ("add_bits" | "sub_bits" | "and_bits" | "or_bits" | "xor_bits" | "mult_vec" | "mults_vec"),
      return_ctyp,
      (0 | 1),
      CT_lbits,
      represented
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
    | ("vector_update" | "vector_update_inc" | "internal_vector_update"), return_ctyp, 0,
      (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), represented
      when is_c_repr_fixed_bytes return_ctyp && ctyp_equal return_ctyp represented ->
        true
    | ("vector_update" | "vector_update_inc" | "internal_vector_update"), return_ctyp, 0, CT_lbits,
      represented
      when is_c_repr_u256 return_ctyp && is_c_repr_u256 represented ->
        true
    | ("vector_update" | "vector_update_inc" | "internal_vector_update"), return_ctyp, 1, CT_lint,
      (CT_fint _ | CT_fuint _)
      when is_c_repr_fixed_bytes return_ctyp
           || is_c_repr_u256 return_ctyp
           || (match return_ctyp with CT_vector _ | CT_fvector _ -> true | _ -> false) ->
        true
    | _ -> false

  (** Convert a sail type into a C-type. This function can be quite slow, because it uses ctx.local_env and SMT to
      analyse the Sail types and attempts to fit them into the smallest possible C types, provided ctx.optimize_smt is
      true (default) **)
  let rec convert_typ ctx typ =
    let c_repr_uint64 = has_c_repr_uint64 ctx.local_env typ in
    let c_repr_int64 = has_c_repr_int64 ctx.local_env typ in
    let c_repr_u256 = has_c_repr_u256 ctx.local_env typ in
    let c_repr_fixed_bytes = find_c_repr_fixed_bytes ctx.local_env typ in
    let (Typ_aux (typ_aux, l) as typ) = Env.expand_synonyms ctx.local_env typ in
    match typ_aux with
    | _ when c_repr_uint64 -> CT_fuint 64
    | _ when c_repr_int64 -> CT_fint 64
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
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
              when Big_int.less_equal Big_int.zero n && Big_int.less_equal m (max_uint 64) ->
                CT_fuint 64
            | Nexp_aux (Nexp_constant n, _), Nexp_aux (Nexp_constant m, _)
              when Big_int.less_equal (min_int 64) n && Big_int.less_equal m (max_int 64) ->
                CT_fint 64
            | n, m ->
                if
                  prove __POS__ ctx.local_env (nc_lteq (nconstant Big_int.zero) n)
                  && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_uint 64)))
                then CT_fuint 64
                else if
                  prove __POS__ ctx.local_env (nc_lteq (nconstant (min_int 64)) n)
                  && prove __POS__ ctx.local_env (nc_lteq m (nconstant (max_int 64)))
                then CT_fint 64
                else CT_lint
          )
      )
    | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> CT_list (ctyp_suprema (convert_typ ctx typ))
    (* When converting a sail bitvector type into C, we have three options in order of efficiency:
       - If the length is obviously static and smaller than 64, use the fixed bits type (aka uint64_t), fbits.
       - If the length is less than 64, then use a small bits type, sbits.
       - If the length may be larger than 64, use a large bits type lbits. *)
    | Typ_app (id, [A_aux (A_nexp n, _)]) when string_of_id id = "bitvector" -> (
        match nexp_simp n with
        | Nexp_aux (Nexp_constant n, _)
          when Opts.specialize_c && Big_int.equal n (Big_int.of_int 256) ->
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
    | Typ_app (id, [A_aux (A_nexp _, _); A_aux (A_typ typ, _)]) when string_of_id id = "vector" ->
        CT_vector (convert_typ ctx typ)
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
        | Local (_, typ) ->
            let ctyp = convert_typ ctx typ in
            (* A [$[c_repr]] newtype payload retains its native representation
               after destructuring even though its semantic type is int/nat. *)
            (match NameMap.find_opt id ctx.locals with
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
            match NameMap.find_opt id ctx.locals with
            | Some (_, ctyp) -> ctyp
            | None -> convert_typ ctx (aval_typ aval)
          )
        | _ -> convert_typ ctx (aval_typ aval)
      )

  (* Map over all the functions in an aexp. *)
  let rec analyze_functions ctx f (AE_aux (aexp, ({ env; _ } as annot))) =
    let ctx = { ctx with local_env = env } in
    let aexp =
      match aexp with
      | AE_app (id, vs, typ) -> f ctx id vs typ
      | AE_typ (aexp, typ) -> AE_typ (analyze_functions ctx f aexp, typ)
      | AE_assign (alexp, aexp) -> AE_assign (alexp, analyze_functions ctx f aexp)
      | AE_short_circuit (op, aval, aexp) -> AE_short_circuit (op, aval, analyze_functions ctx f aexp)
      | AE_let (mut, id, typ1, aexp1, (AE_aux (_, { env = env2; _ }) as aexp2), typ2) ->
          let aexp1 = analyze_functions ctx f aexp1 in
          (* Use aexp2's environment because it will contain constraints for id *)
          let semantic_ctyp1 = convert_typ { ctx with local_env = env2 } typ1 in
          let ctyp1 =
            match (semantic_ctyp1, aexp1) with
            | semantic, AE_aux (AE_val aval, _) -> (
                match c_aval ctx aval with
                | AV_cval (cval, _) when representation_refines ~semantic ~represented:(cval_ctyp cval) ->
                    cval_ctyp cval
                | _ -> semantic
              )
            | semantic, AE_aux (AE_app (call, args, _), _) -> (
                let external_id =
                  match call with
                  | Sail_function id when ctx_is_extern id ctx -> Some (mk_id (ctx_get_extern id ctx))
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
                match external_id with
                | Some id -> specialize_call_result id arg_ctyps semantic
                | None -> semantic
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
          AE_let (mut, id, typ1, aexp1, analyze_functions ctx f aexp2, typ2)
      | AE_block (aexps, aexp, typ) ->
          AE_block (List.map (analyze_functions ctx f) aexps, analyze_functions ctx f aexp, typ)
      | AE_if (aval, aexp1, aexp2, typ) ->
          AE_if (aval, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2, typ)
      | AE_loop (loop_typ, aexp1, aexp2) ->
          AE_loop (loop_typ, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2)
      | AE_for (id, aexp1, aexp2, aexp3, order, aexp4) ->
          let aexp1 = analyze_functions ctx f aexp1 in
          let aexp2 = analyze_functions ctx f aexp2 in
          let aexp3 = analyze_functions ctx f aexp3 in
          (* Currently we assume that loop indexes are always safe to put into an int64 *)
          let ctx = { ctx with locals = NameMap.add id (Immutable, CT_fint 64) ctx.locals } in
          let aexp4 = analyze_functions ctx f aexp4 in
          AE_for (id, aexp1, aexp2, aexp3, order, aexp4)
      | AE_match (aval, cases, typ) ->
          let merge_pattern_bindings left right =
            NameMap.fold (fun id ctyp bindings -> NameMap.add id ctyp bindings) right left
          in
          let merge_all_pattern_bindings bindings =
            List.fold_left
              (fun merged bindings ->
                Option.bind merged (fun merged ->
                    Option.map (merge_pattern_bindings merged) bindings
                )
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
                      (List.map
                         (fun (field, pat) -> represented_pattern_bindings (field_ctyp field) pat)
                         fields
                      )
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
                  | None ->
                      NameMap.bindings (NameMap.map (convert_typ ctx) (apat_types pat))
                )
              | None -> NameMap.bindings (NameMap.map (convert_typ ctx) (apat_types pat))
            in
            let ctx =
              List.fold_left
                (fun ctx (id, ctyp) -> { ctx with locals = NameMap.add id (Immutable, ctyp) ctx.locals })
                ctx pat_bindings
            in
            (pat, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2, uannot)
          in
          AE_match (aval, List.map analyze_case cases, typ)
      | AE_try (aexp, cases, typ) ->
          AE_try
            ( analyze_functions ctx f aexp,
              List.map
                (fun (pat, aexp1, aexp2, uannot) ->
                  (pat, analyze_functions ctx f aexp1, analyze_functions ctx f aexp2, uannot)
                )
                cases,
              typ
            )
      | (AE_field _ | AE_struct_update _ | AE_val _ | AE_return _ | AE_exit _ | AE_throw _) as v -> v
    in
    AE_aux (aexp, annot)

  let analyze_primop' ctx id args typ =
    let no_change = AE_app (Sail_function id, args, typ) in
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
      else
        match
          if is_fixed_integer left_ctyp then
            Option.map (fun right -> (left, right)) (integer_literal_as left_ctyp right)
          else None
        with
        | Some aligned -> Some aligned
        | None ->
            if is_fixed_integer right_ctyp then
              Option.map (fun left -> (left, right)) (integer_literal_as right_ctyp left)
            else None
    in
    let native_binary op left right =
      Option.map (fun (left, right) -> AE_val (AV_cval (V_call (op, [left; right]), typ)))
        (align_fixed_integers left right)
    in
    let native_binary_or_no_change op left right =
      Option.value (native_binary op left right) ~default:no_change
    in
    let native_unsigned_binary_or_no_change op left right =
      match align_fixed_integers left right with
      | Some (left, right)
        when (match (cval_ctyp left, cval_ctyp right) with CT_fuint _, CT_fuint _ -> true | _ -> false) ->
          AE_val (AV_cval (V_call (op, [left; right]), typ))
      | _ -> no_change
    in
    let native_shift_amount = function
      | V_lit (VL_int value, _)
        when Big_int.less_equal Big_int.zero value && Big_int.less_equal value (max_uint 64) ->
          Some (V_lit (VL_int value, CT_fuint 64))
      | amount when is_fixed_integer (cval_ctyp amount) -> Some amount
      | _ -> None
    in

    match (extern, args) with
    | "neg_int", [AV_cval (V_lit (VL_int value, _), _)] -> (
        match convert_typ ctx typ with
        | (CT_fint _ as result_ctyp) -> (
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
    | "eq_int", [AV_cval (v1, _); AV_cval (v2, _)] -> native_binary_or_no_change Eq v1 v2
    | "neq_int", [AV_cval (v1, _); AV_cval (v2, _)] -> native_binary_or_no_change Neq v1 v2
    | "eq_bit", [AV_cval (v1, _); AV_cval (v2, _)] -> AE_val (AV_cval (V_call (Eq, [v1; v2]), typ))
    | "zeros", [_] -> (
        match destruct_bitvector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) when Big_int.less_equal n (Big_int.of_int 64) ->
            let n = Big_int.to_int n in
            AE_val (AV_cval (V_lit (VL_bits (Util.list_init n (fun _ -> Sail2_values.B0)), CT_fbits n), typ))
        | _ -> no_change
      )
    | "zero_extend", [AV_cval (v, _); _] -> (
        match destruct_bitvector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) when Big_int.less_equal n (Big_int.of_int 64) ->
            AE_val (AV_cval (V_call (Zero_extend (Big_int.to_int n), [v]), typ))
        | _ -> no_change
      )
    | "sign_extend", [AV_cval (v, _); _] -> (
        match destruct_bitvector ctx.tc_env typ with
        | Some (Nexp_aux (Nexp_constant n, _)) when Big_int.less_equal n (Big_int.of_int 64) ->
            AE_val (AV_cval (V_call (Sign_extend (Big_int.to_int n), [v]), typ))
        | _ -> no_change
      )
    | "lteq", [AV_cval (v1, _); AV_cval (v2, _)] -> native_binary_or_no_change Ilteq v1 v2
    | "gteq", [AV_cval (v1, _); AV_cval (v2, _)] -> native_binary_or_no_change Igteq v1 v2
    | "lt", [AV_cval (v1, _); AV_cval (v2, _)] -> native_binary_or_no_change Ilt v1 v2
    | "gt", [AV_cval (v1, _); AV_cval (v2, _)] -> native_binary_or_no_change Igt v1 v2
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
    | ("shiftl" | "shiftr" | "arith_shiftr" as shift), [AV_cval (value, _); AV_cval (amount, _)] -> (
        match (cval_ctyp value, native_shift_amount amount) with
        | CT_fbits 0, Some _ when shift = "arith_shiftr" -> no_change
        | CT_fbits _, Some amount ->
            let op =
              match shift with
              | "shiftl" -> Bvshiftl
              | "shiftr" -> Bvshiftr
              | "arith_shiftr" -> Bvarith_shiftr
              | _ -> assert false
            in
            AE_val (AV_cval (V_call (op, [value; amount]), typ))
        | _ -> no_change
      )
    | "sail_unsigned", [AV_cval (value, _)] -> (
        match cval_ctyp value with
        | CT_fbits _ -> AE_val (AV_cval (V_call (Unsigned 64, [value]), typ))
        | _ -> no_change
      )
    | "sail_signed", [AV_cval (value, _)] -> (
        match cval_ctyp value with
        | CT_fbits _ -> AE_val (AV_cval (V_call (Signed 64, [value]), typ))
        | _ -> no_change
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
    | "get_slice_int", [_; AV_cval (value, _); AV_cval (start, _)] -> (
        match (convert_typ ctx typ, cval_ctyp value, native_shift_amount start) with
        | CT_fbits n, CT_fuint _, Some start when n <= 64 ->
            (* A non-negative bounded integer already has the same low-bit
               encoding as its uint64_t representation.  Keep this common
               nat/range -> bits bridge native instead of materialising a
               GMP integer merely to extract at most one limb. *)
            AE_val (AV_cval (V_call (Slice n, [value; start]), typ))
        | _ -> no_change
      )
    | "vector_access", [AV_cval (vec, _); AV_cval (n, _)]
      when (match cval_ctyp vec with CT_fbits _ | CT_sbits _ -> true | ctyp -> is_c_repr_u256 ctyp) ->
        AE_val (AV_cval (V_call (Bvaccess, [vec; n]), typ))
    | "vector_access", [v; AV_cval (n, _)] -> (
        match destruct_vector ctx.tc_env (aval_typ v) with
        | Some (_, elem_typ) -> (
            match cval_ctyp n with
            | CT_fint 64 -> AE_app (Pure_extern (mk_id "fast_vector_access", Some elem_typ), args, typ)
            | CT_fuint 64 ->
                AE_app (Pure_extern (mk_id "fast_unsigned_vector_access", Some elem_typ), args, typ)
            | _ -> no_change
          )
        | None -> no_change
      )
    | (("add_int" | "sub_int" | "mult_int" | "tdiv_int" | "tmod_int") as f),
      [AV_cval (op1, _); AV_cval (op2, _)] ->
        let op =
          match f with
          | "add_int" -> Iadd
          | "sub_int" -> Isub
          | "mult_int" -> Imul
          | "tdiv_int" -> Idiv
          | "tmod_int" -> Imod
          | _ -> assert false
        in
        native_binary_or_no_change op op1 op2
    | ("mult_vec" | "mults_vec"), [AV_cval (op1, _); AV_cval (op2, _)]
      when is_c_repr_u256 (cval_ctyp op1) && ctyp_equal (cval_ctyp op1) (cval_ctyp op2) ->
        (* Both operations agree modulo 2^256 when the result width is 256.
           The backend helper computes exactly those low four limbs. *)
        AE_val (AV_cval (V_call (Imul, [op1; op2]), typ))
    | (("ediv_int" | "emod_int") as f), [AV_cval (op1, _); AV_cval (op2, _)] ->
        native_unsigned_binary_or_no_change (if f = "ediv_int" then Idiv else Imod) op1 op2
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

  let analyze_primop ctx id args typ =
    let no_change = AE_app (id, args, typ) in
    match id with
    | Sail_function id ->
        if !optimize_primops then (try analyze_primop' ctx id args typ with Failure _ -> no_change) else no_change
    | _ -> no_change

  let optimize_anf ctx aexp = analyze_functions ctx analyze_primop (c_literals ctx aexp)

  let unroll_loops = None
  let make_call_precise _ _ _ _ = true
  let ignore_64 = false
  let struct_value = false
  let tuple_value = false
  let use_real = false
  let branch_coverage = Opts.branch_coverage
  let track_throw = true
  let assert_to_exception = Opts.assert_to_exception
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
      let gs = ngensym () in
      match Bindings.find_opt id ret_ctyps with
      | None -> raise (Reporting.err_general (id_loc id) ("Cannot find return type for function " ^ string_of_id id))
      | Some ret_ctyp when not (is_stack_ctyp ctx ret_ctyp) ->
          CDEF_aux (CDEF_fundef (id, Return_via gs, args, fix_early_heap_return gs body), def_annot)
          :: insert_heap_returns ctx ret_ctyps cdefs
      | Some ret_ctyp ->
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

let optimize ~have_rts ctx recursive_functions cdefs =
  let nothing cdefs = cdefs in
  cdefs
  |> (if !optimize_alias then List.concat_map remove_alias else nothing)
  |> (if !optimize_alias then combine_variables ctx else nothing)
  (* We need the runtime to initialize hoisted allocations *)
  |> ( if !optimize_hoist_allocations && have_rts then List.concat_map (hoist_allocations recursive_functions)
       else nothing
     )
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
  val c_repr_uint64 : IdSet.t
  val c_repr_int64 : IdSet.t
  val c_repr_u256 : IdSet.t
  val c_repr_fixed_bytes : int Bindings.t
  val specialize_c : bool
  val cpp : bool
  val cpp_class_name : string
  val cpp_namespace : string
  val cpp_derive_from : string option
end

module Codegen (Config : CODEGEN_CONFIG) = struct
  open Printf

  let has_prefix prefix s =
    if String.length s < String.length prefix then false else String.sub s 0 (String.length prefix) = prefix

  let has_bad_prefix s =
    has_prefix "sail_" s || has_prefix "Sail_" s || has_prefix "SAIL_" s || has_prefix "undefined_" s

  (* Prefix to function name in definitions. *)
  let class_impl_prefix () = if Config.cpp then Config.cpp_class_name ^ "::" else ""

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

        let mangle () s = Util.zencode_string s

        let variant s = function 0 -> s | n -> s ^ string_of_int n

        let overrides = Config.overrides
      end)
      ()

  let sgen_id id = NameGen.to_string () id

  let sgen_uid (id, ctyps) =
    match ctyps with
    | [] -> NameGen.to_string () id
    | _ -> NameGen.translate () (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

  let sgen_name =
    let ssa_num n = if n = -1 then "" else "/" ^ string_of_int n in
    function
    | Gen (v1, v2, n) -> NameGen.to_string () (mk_id (sprintf "%d.%d" v1 v2)) ^ ssa_num n
    | Name (id, n) -> NameGen.to_string () id ^ ssa_num n
    | Abstract id -> NameGen.to_string ~prefix:"abstract_" () id
    | Have_exception n -> "have_exception" ^ ssa_num n
    | Return n -> "return" ^ ssa_num n
    | Current_exception n -> "(*current_exception)" ^ ssa_num n
    | Throw_location n -> "throw_location" ^ ssa_num n
    | Memory_writes n -> "memory_writes" ^ ssa_num n
    | Channel (chan, n) -> (
        match chan with Chan_stdout -> "stdout" ^ ssa_num n | Chan_stderr -> "stderr" ^ ssa_num n
      )

  let codegen_id id = string (sgen_id id)

  let sgen_function_id id =
    let str = NameGen.to_string () id in
    if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)

  let sgen_function_uid uid =
    let str = sgen_uid uid in
    if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)

  let codegen_function_id id = string (sgen_function_id id)

  let rec sgen_ctyp = function
    | ctyp when is_c_repr_u256 ctyp -> "sail_u256"
    | ctyp when is_c_repr_fixed_bytes ctyp ->
        "sail_fixed_bytes_" ^ string_of_int (Option.get (c_repr_fixed_bytes_length ctyp))
    | CT_unit -> "unit"
    | CT_bool -> "bool"
    | CT_fbits _ -> "uint64_t"
    | CT_sbits _ -> "sbits"
    | CT_fint _ -> "int64_t"
    | CT_fuint _ -> "uint64_t"
    | CT_constant _ -> "int64_t"
    | CT_lint -> "sail_int"
    | CT_lbits -> "lbits"
    | CT_tup _ as tup -> "struct " ^ Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
    | CT_struct (id, _) -> "struct " ^ sgen_id id
    | CT_enum id -> "enum " ^ sgen_id id
    | CT_variant (id, _) -> "struct " ^ sgen_id id
    | CT_list _ as l -> Util.zencode_string (string_of_ctyp l)
    | CT_vector _ as v -> Util.zencode_string (string_of_ctyp v)
    | CT_fvector (_, typ) -> sgen_ctyp (CT_vector typ)
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
    | ctyp when is_c_repr_u256 ctyp -> "u256"
    | ctyp when is_c_repr_fixed_bytes ctyp ->
        "fixed_bytes_" ^ string_of_int (Option.get (c_repr_fixed_bytes_length ctyp))
    | CT_unit -> "unit"
    | CT_bool -> "bool"
    | CT_fbits _ -> "fbits"
    | CT_sbits _ -> "sbits"
    | CT_fint _ -> "mach_int"
    | CT_fuint _ -> "mach_uint"
    | CT_constant _ -> "mach_int"
    | CT_lint -> "sail_int"
    | CT_lbits -> "lbits"
    | CT_tup _ as tup -> Util.zencode_string ("tuple_" ^ string_of_ctyp tup)
    | CT_struct (id, _) -> sgen_id id
    | CT_enum id -> sgen_id id
    | CT_variant (id, _) -> sgen_id id
    | CT_list _ as l -> Util.zencode_string (string_of_ctyp l)
    | CT_vector _ as v -> Util.zencode_string (string_of_ctyp v)
    | CT_fvector (_, typ) -> sgen_ctyp_name (CT_vector typ)
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
            else
              match rest with
              | bit :: rest -> take (n - 1) (bit :: acc) rest
              | [] -> assert false
          in
          let chunk, rest = take size [] bits in
          chunk :: chunks size rest
    in
    let limbs =
      chunks 64 padded
      |> List.rev
      |> List.map (fun limb -> "UINT64_C(" ^ Sail2_values.show_bitlist limb ^ ")")
    in
    "((sail_u256){{" ^ String.concat ", " limbs ^ "}})"

  let sgen_value ctyp = function
    | VL_bits bs when is_c_repr_u256 ctyp -> sgen_u256_bits bs
    | VL_bits [] -> "UINT64_C(0)"
    | VL_bits bs -> "UINT64_C(" ^ Sail2_values.show_bitlist bs ^ ")"
    | VL_int i -> (
        match ctyp with
        | CT_fuint _ -> "UINT64_C(" ^ Big_int.to_string i ^ ")"
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

  and sgen_call op cvals =
    match (op, cvals) with
    | Bnot, [v] -> "!(" ^ sgen_cval v ^ ")"
    | Band, vs -> "(" ^ Util.string_of_list " && " sgen_cval vs ^ ")"
    | Bor, vs -> "(" ^ Util.string_of_list " || " sgen_cval vs ^ ")"
    | List_hd, [v] -> sprintf "(%s).hd" ("*" ^ sgen_cval v)
    | List_tl, [v] -> sprintf "(%s).tl" ("*" ^ sgen_cval v)
    | List_is_empty, [v] -> sprintf "(%s == NULL)" (sgen_cval v)
    | Eq, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_sbits _ -> sprintf "eq_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_value ctyp ->
            sprintf "eq_%s(%s, %s)" (sgen_ctyp_name ctyp) (sgen_cval v1) (sgen_cval v2)
        | _ -> sprintf "(%s == %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Neq, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_sbits _ -> sprintf "neq_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_value ctyp ->
            sprintf "(!eq_%s(%s, %s))" (sgen_ctyp_name ctyp) (sgen_cval v1) (sgen_cval v2)
        | _ -> sprintf "(%s != %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Ilt, [v1; v2] -> sprintf "(%s < %s)" (sgen_cval v1) (sgen_cval v2)
    | Igt, [v1; v2] -> sprintf "(%s > %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilteq, [v1; v2] -> sprintf "(%s <= %s)" (sgen_cval v1) (sgen_cval v2)
    | Igteq, [v1; v2] -> sprintf "(%s >= %s)" (sgen_cval v1) (sgen_cval v2)
    | Iadd, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fuint _ -> sprintf "sail_checked_u64_add(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fint _ -> sprintf "sail_checked_i64_add(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> sprintf "(%s + %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Isub, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fuint _ -> sprintf "sail_checked_u64_sub(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fint _ -> sprintf "sail_checked_i64_sub(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> sprintf "(%s - %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Imul, [v1; v2] when is_c_repr_u256 (cval_ctyp v1) ->
        sprintf "u256_mul(%s, %s)" (sgen_cval v1) (sgen_cval v2)
    | Imul, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fuint _ -> sprintf "sail_checked_u64_mul(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fint _ -> sprintf "sail_checked_i64_mul(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> sprintf "(%s * %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Idiv, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fuint _ -> sprintf "sail_checked_u64_div(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fint _ -> sprintf "sail_checked_i64_div(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> sprintf "(%s / %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Imod, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fuint _ -> sprintf "sail_checked_u64_mod(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_fint _ -> sprintf "sail_checked_i64_mod(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> sprintf "(%s %% %s)" (sgen_cval v1) (sgen_cval v2)
      )
    | Unsigned 64, [vec] -> sprintf "((uint64_t) %s)" (sgen_cval vec)
    | Signed 64, [vec] -> (
        match cval_ctyp vec with CT_fbits n -> sprintf "fast_signed(%s, %d)" (sgen_cval vec) n | _ -> assert false
      )
    | Bvand, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fbits _ -> sprintf "(%s & %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_sbits _ -> sprintf "and_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_and(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> assert false
      )
    | Bvnot, [v] -> (
        match cval_ctyp v with
        | CT_fbits n -> sprintf "(~(%s) & %s)" (sgen_cval v) (sgen_cval (v_mask_lower n))
        | CT_sbits _ -> sprintf "not_sbits(%s)" (sgen_cval v)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_not(%s)" (sgen_cval v)
        | _ -> assert false
      )
    | Bvor, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fbits _ -> sprintf "(%s | %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_sbits _ -> sprintf "or_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | ctyp when is_c_repr_u256 ctyp -> sprintf "u256_or(%s, %s)" (sgen_cval v1) (sgen_cval v2)
        | _ -> assert false
      )
    | Bvxor, [v1; v2] -> (
        match cval_ctyp v1 with
        | CT_fbits _ -> sprintf "(%s ^ %s)" (sgen_cval v1) (sgen_cval v2)
        | CT_sbits _ -> sprintf "xor_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
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
            sprintf "((%s >= UINT64_C(64)) ? UINT64_C(0) : ((%s << %s) & %s))"
              (sgen_cval amount) (sgen_cval value) (sgen_cval amount) (sgen_mask width)
        | _ -> assert false
      )
    | Bvshiftr, [value; amount] -> (
        match cval_ctyp value with
        | CT_fbits _ -> sprintf "safe_rshift(%s, %s)" (sgen_cval value) (sgen_cval amount)
        | _ -> assert false
      )
    | Bvarith_shiftr, [value; amount] -> (
        match cval_ctyp value with
        | CT_fbits width ->
            let mask = sgen_mask width in
            let sign = sprintf "((%s >> %d) & UINT64_C(1))" (sgen_cval value) (width - 1) in
            sprintf
              "((%s >= UINT64_C(%d)) ? (%s ? %s : UINT64_C(0)) : (safe_rshift(%s, %s) | (%s ? (%s ^ safe_rshift(%s, %s)) : UINT64_C(0))))"
              (sgen_cval amount) width sign mask (sgen_cval value) (sgen_cval amount) sign mask mask
              (sgen_cval amount)
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
        | CT_fbits _ -> sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & (%s >> %s))" len (sgen_cval vec) (sgen_cval start)
        | CT_fuint _ ->
            sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & safe_rshift(%s, %s))" len (sgen_cval vec)
              (sgen_cval start)
        | CT_sbits _ ->
            sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & (%s.bits >> %s))" len (sgen_cval vec) (sgen_cval start)
        | ctyp when is_c_repr_u256 ctyp ->
            let extracted = sprintf "u256_extract_u64(%s, (uint64_t)(%s))" (sgen_cval vec) (sgen_cval start) in
            if len = 64 then extracted else sprintf "(%s & %s)" (sgen_mask len) extracted
        | _ -> assert false
      )
    | Sslice 64, [vec; start; len] -> (
        match cval_ctyp vec with
        | CT_fbits _ -> sprintf "sslice(%s, %s, %s)" (sgen_cval vec) (sgen_cval start) (sgen_cval len)
        | CT_sbits _ -> sprintf "sslice(%s.bits, %s, %s)" (sgen_cval vec) (sgen_cval start) (sgen_cval len)
        | _ -> assert false
      )
    | Set_slice, [vec; start; slice] -> (
        match (cval_ctyp vec, cval_ctyp slice) with
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
    | CL_id (Current_exception _, _) -> "current_exception"
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
    | ctyp -> sail_equal (sgen_ctyp_name ctyp) "%s, %s" arg1 arg2

  let monomorphic_id_base id =
    let name = string_of_id id in
    match String.index_opt name '<' with Some i -> String.sub name 0 i | None -> name

  let matching_variant_constructors l ctx ctyp_to ctyp_from =
    let variant_to, constructors_to = variant_constructor_bindings l ctx ctyp_to in
    let variant_from, constructors_from = variant_constructor_bindings l ctx ctyp_from in
    if monomorphic_id_base variant_to <> monomorphic_id_base variant_from then None
    else
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
    | to_typ, CT_lbits when is_c_repr_u256 to_typ ->
        ksprintf string "  %s = u256_of_lbits(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | CT_lbits, from_typ when is_c_repr_u256 from_typ ->
        ksprintf string "  lbits_of_u256(%s, %s);" (sgen_clexp l clexp) (sgen_cval cval)
    | to_typ, CT_fbits _ when is_c_repr_u256 to_typ ->
        ksprintf string "  %s = u256_of_fbits(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8))
      when is_c_repr_fixed_bytes to_typ ->
        let length = Option.get (c_repr_fixed_bytes_length to_typ) in
        let i = ngensym () in
        ksprintf string "  for (size_t %s = 0; %s < %d; ++%s) {" (sgen_name i) (sgen_name i) length (sgen_name i)
        ^^ hardline
        ^^ ksprintf string "    %s.bytes[%s] = (uint8_t)(%s.data[%s] & UINT64_C(0xff));"
             (sgen_clexp_pure l clexp) (sgen_name i) (sgen_cval cval) (sgen_name i)
        ^^ hardline ^^ string "  }"
    | (CT_vector (CT_fbits 8) | CT_fvector (_, CT_fbits 8)), from_typ
      when is_c_repr_fixed_bytes from_typ ->
        let length = Option.get (c_repr_fixed_bytes_length from_typ) in
        let i = ngensym () in
        sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) "%s" (sgen_clexp l clexp)
        ^^ hardline
        ^^ ksprintf string "  internal_vector_init_%s(%s, INT64_C(%d));" (sgen_ctyp_name ctyp_to)
             (sgen_clexp l clexp) length
        ^^ hardline
        ^^ ksprintf string "  for (size_t %s = 0; %s < %d; ++%s) {" (sgen_name i) (sgen_name i) length (sgen_name i)
        ^^ hardline
        ^^ ksprintf string "    %s.data[%s] = (uint64_t)%s.bytes[%s];" (sgen_clexp_pure l clexp)
             (sgen_name i) (sgen_cval cval) (sgen_name i)
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
                ( if is_stack_ctyp ctx payload_to then empty
                  else
                    hardline
                    ^^ sail_create ~suffix:";" (sgen_ctyp_name payload_to) "&%s" (sgen_name converted)
                )
              in
              let conversion =
                codegen_conversion l ctx (CL_id (converted, payload_to)) source_payload
              in
              let construct =
                ksprintf string "%s(%s%s, %s);" (sgen_function_uid (constructor_to, []))
                  (extra_arguments false) (sgen_clexp l clexp) (sgen_name converted)
              in
              let cleanup =
                if is_stack_ctyp ctx payload_to then empty
                else sail_kill ~suffix:";" (sgen_ctyp_name payload_to) "&%s" (sgen_name converted)
              in
              ( ksprintf string "Kind_%s" (sgen_id constructor_from),
                [declaration; conversion; construct; cleanup]
              )
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
        let special_extern = match extern_info with Extern _ -> true | Call -> false in
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
          | "internal_pick", _ -> sprintf "pick_%s" (sgen_ctyp_name ctyp)
          | "sail_cons", _ -> (
              match Option.map cval_ctyp (List.nth_opt args 0) with
              | Some ctyp ->
                  Util.zencode_string ("cons#" ^ string_of_ctyp (ctyp_suprema_for_c Config.specialize_c ctyp))
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
                     || match cval_ctyp value with CT_vector _ | CT_fvector _ -> true | _ -> false)
                     && ctyp_equal (cval_ctyp index) (CT_fuint 64) ->
                  sprintf "fast_unsigned_vector_access_%s" (sgen_ctyp_name (cval_ctyp value))
              | value :: index :: _
                when (is_c_repr_u256 (cval_ctyp value)
                     || is_c_repr_fixed_bytes (cval_ctyp value)
                     || match cval_ctyp value with CT_vector _ | CT_fvector _ -> true | _ -> false)
                     && ctyp_equal (cval_ctyp index) (CT_fint 64) ->
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
            when is_c_repr_fixed_bytes ctyp
                 || (match ctyp with CT_vector _ | CT_fvector _ -> true | _ -> false) -> (
              match List.nth_opt args 0 with
              | Some length when ctyp_equal (cval_ctyp length) (CT_fuint 64) ->
                  sprintf "fast_unsigned_vector_init_%s" (sgen_ctyp_name ctyp)
              | Some length when ctyp_equal (cval_ctyp length) (CT_fint 64) ->
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
              | Some index when ctyp_equal (cval_ctyp index) (CT_fuint 64) -> "u256_update_u64"
              | Some index when ctyp_equal (cval_ctyp index) (CT_fint 64) -> "u256_update_i64"
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update", ctyp when is_c_repr_fixed_bytes ctyp -> (
              match List.nth_opt args 1 with
              | Some index when ctyp_equal (cval_ctyp index) (CT_fuint 64) ->
                  sprintf "fast_unsigned_vector_update_%s" (sgen_ctyp_name ctyp)
              | Some index when ctyp_equal (cval_ctyp index) (CT_fint 64) ->
                  sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update", ((CT_vector _ | CT_fvector _) as ctyp) -> (
              match List.nth_opt args 1 with
              | Some index when ctyp_equal (cval_ctyp index) (CT_fuint 64) ->
                  sprintf "fast_unsigned_vector_update_%s" (sgen_ctyp_name ctyp)
              | Some index when ctyp_equal (cval_ctyp index) (CT_fint 64) ->
                  sprintf "fast_vector_update_%s" (sgen_ctyp_name ctyp)
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update", _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
          | "vector_update_inc", CT_fbits _ -> "update_fbits_inc"
          | "vector_update_inc", CT_lbits -> "update_lbits_inc"
          | "vector_update_inc", ctyp when is_c_repr_u256 ctyp -> (
              match List.nth_opt args 1 with
              | Some index when ctyp_equal (cval_ctyp index) (CT_fuint 64) -> "u256_update_u64"
              | Some index when ctyp_equal (cval_ctyp index) (CT_fint 64) -> "u256_update_i64"
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update_inc", ctyp when is_c_repr_fixed_bytes ctyp -> (
              match List.nth_opt args 1 with
              | Some index when ctyp_equal (cval_ctyp index) (CT_fuint 64) ->
                  sprintf "fast_unsigned_vector_update_%s" (sgen_ctyp_name ctyp)
              | Some index when ctyp_equal (cval_ctyp index) (CT_fint 64) ->
                  sprintf "internal_vector_update_%s" (sgen_ctyp_name ctyp)
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | "vector_update_inc", ((CT_vector _ | CT_fvector _) as ctyp) -> (
              match List.nth_opt args 1 with
              | Some index when ctyp_equal (cval_ctyp index) (CT_fuint 64) ->
                  sprintf "fast_unsigned_vector_update_%s" (sgen_ctyp_name ctyp)
              | Some index when ctyp_equal (cval_ctyp index) (CT_fint 64) ->
                  sprintf "fast_vector_update_%s" (sgen_ctyp_name ctyp)
              | _ -> sprintf "vector_update_%s" (sgen_ctyp_name ctyp)
            )
          | ("shiftl" | "shiftr" | "arith_shiftr" as shift), ctyp when is_c_repr_u256 ctyp ->
              let suffix =
                match List.nth_opt args 1 with
                | Some amount when ctyp_equal (cval_ctyp amount) (CT_fuint 64) -> "_u64"
                | Some amount when ctyp_equal (cval_ctyp amount) (CT_fint 64) -> "_i64"
                | _ -> ""
              in
              "u256_" ^ shift ^ suffix
          | "zero_extend", ctyp when is_c_repr_u256 ctyp -> (
              match List.nth_opt args 0 with
              | Some value when (match cval_ctyp value with CT_fbits _ -> true | _ -> false) -> "u256_of_fbits"
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
              match args with
              | cval :: _ when is_c_repr_u256 (cval_ctyp cval) -> "u256_unsigned"
              | _ -> fname
            )
          | "sail_signed", _ -> (
              match args with
              | cval :: _ when is_c_repr_u256 (cval_ctyp cval) -> "u256_signed"
              | _ -> fname
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
          | "zero_extend", ctyp, value :: _
            when is_c_repr_u256 ctyp
                 && (match cval_ctyp value with CT_fbits _ | CT_lbits -> true | _ -> false) ->
              sgen_cval value
          | _ -> default_c_args
        in
        if fname = "reg_deref" then
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
          | ctyp when is_c_repr_u256 ctyp -> ("u256_zero()", [])
          | ctyp when is_c_repr_fixed_bytes ctyp ->
              (sprintf "%s_zero()" (sgen_ctyp_name ctyp), [])
          | CT_unit -> ("UNIT", [])
          | CT_fint _ -> ("INT64_C(0xdeadc0de)", [])
          | CT_fuint _ -> ("UINT64_C(0xdeadc0de)", [])
          | CT_lint when !optimize_fixed_int -> ("((sail_int) 0xdeadc0de)", [])
          | CT_fbits 1 -> ("UINT64_C(0)", [])
          | CT_fbits _ -> ("UINT64_C(0xdeadc0de)", [])
          | CT_sbits _ -> ("undefined_sbits()", [])
          | CT_lbits when !optimize_fixed_bits -> ("undefined_lbits(false)", [])
          | CT_bool -> ("false", [])
          | CT_enum _ -> (sprintf "((%s)0)" (sgen_ctyp ctyp), [])
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
          StaticFunctionDefinition struct_copy;
        ]
        @ ( if not (is_stack_ctyp ctx struct_ctyp) then
              [
                StaticFunctionDefinition (derive sail_create);
                StaticFunctionDefinition (derive sail_recreate);
                StaticFunctionDefinition (derive sail_kill);
              ]
            else []
          )
        @ [StaticFunctionDefinition struct_eq]
    | CTD_variant (id, _, tus) ->
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
          StaticFunctionDefinition codegen_init;
          StaticFunctionDefinition codegen_reinit;
          StaticFunctionDefinition codegen_clear;
          StaticFunctionDefinition codegen_setter;
          StaticFunctionDefinition codegen_eq;
        ]
        @ List.map (fun tu -> StaticFunctionDefinition (codegen_ctor tu)) tus
        (* If this is the exception type, then we setup up some global variables to deal with exceptions. *)
        @
        if string_of_id id = "exception" then
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

  let checked_native_int_id = mk_id "__sail_checked_native_int"

  let codegen_checked_native_int () =
    if IdSet.mem checked_native_int_id !generated then []
    else (
      generated := IdSet.add checked_native_int_id !generated;
      [
        StaticFunctionDefinition
          (string
             {|
static inline void sail_checked_native_failure(const char *operation) {
  fprintf(stderr, "Sail C backend: %s\n", operation);
  exit(EXIT_FAILURE);
}

static inline uint64_t sail_checked_u64_add(const uint64_t lhs, const uint64_t rhs) {
  if (rhs > UINT64_MAX - lhs) sail_checked_native_failure("uint64_t addition overflow");
  return lhs + rhs;
}

static inline uint64_t sail_checked_u64_sub(const uint64_t lhs, const uint64_t rhs) {
  if (lhs < rhs) sail_checked_native_failure("uint64_t subtraction underflow");
  return lhs - rhs;
}

static inline uint64_t sail_checked_u64_mul(const uint64_t lhs, const uint64_t rhs) {
  if (lhs != UINT64_C(0) && rhs > UINT64_MAX / lhs) {
    sail_checked_native_failure("uint64_t multiplication overflow");
  }
  return lhs * rhs;
}

static inline uint64_t sail_checked_u64_div(const uint64_t lhs, const uint64_t rhs) {
  if (rhs == UINT64_C(0)) sail_checked_native_failure("uint64_t division by zero");
  return lhs / rhs;
}

static inline uint64_t sail_checked_u64_mod(const uint64_t lhs, const uint64_t rhs) {
  if (rhs == UINT64_C(0)) sail_checked_native_failure("uint64_t modulo by zero");
  return lhs % rhs;
}

static inline int64_t sail_checked_i64_add(const int64_t lhs, const int64_t rhs) {
  const __int128 result = (__int128)lhs + (__int128)rhs;
  if (result < (__int128)INT64_MIN || result > (__int128)INT64_MAX) {
    sail_checked_native_failure("int64_t addition overflow");
  }
  return (int64_t)result;
}

static inline int64_t sail_checked_i64_sub(const int64_t lhs, const int64_t rhs) {
  const __int128 result = (__int128)lhs - (__int128)rhs;
  if (result < (__int128)INT64_MIN || result > (__int128)INT64_MAX) {
    sail_checked_native_failure("int64_t subtraction overflow");
  }
  return (int64_t)result;
}

static inline int64_t sail_checked_i64_mul(const int64_t lhs, const int64_t rhs) {
  const __int128 result = (__int128)lhs * (__int128)rhs;
  if (result < (__int128)INT64_MIN || result > (__int128)INT64_MAX) {
    sail_checked_native_failure("int64_t multiplication overflow");
  }
  return (int64_t)result;
}

static inline int64_t sail_checked_i64_div(const int64_t lhs, const int64_t rhs) {
  if (rhs == INT64_C(0)) sail_checked_native_failure("int64_t division by zero");
  if (lhs == INT64_MIN && rhs == INT64_C(-1)) {
    sail_checked_native_failure("int64_t division overflow");
  }
  return lhs / rhs;
}

static inline int64_t sail_checked_i64_mod(const int64_t lhs, const int64_t rhs) {
  if (rhs == INT64_C(0)) sail_checked_native_failure("int64_t modulo by zero");
  if (lhs == INT64_MIN && rhs == INT64_C(-1)) {
    sail_checked_native_failure("int64_t modulo overflow");
  }
  return lhs % rhs;
}
|});
      ]
    )

  let codegen_u256 () =
    if IdSet.mem c_repr_u256_id !generated then []
    else (
      generated := IdSet.add c_repr_u256_id !generated;
      let typedef =
        string
          {|
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
  lbits bits;
  CREATE(lbits)(&bits);
  lbits_of_u256(&bits, value);
  sail_unsigned(result, bits);
  KILL(lbits)(&bits);
}

static inline void u256_signed(sail_int *result, const sail_u256 value) {
  lbits bits;
  CREATE(lbits)(&bits);
  lbits_of_u256(&bits, value);
  sail_signed(result, bits);
  KILL(lbits)(&bits);
}
|}
      in
      let helpers =
        base_helpers
        ^^ (if !emit_generic_lbits_helpers then generic_lbits_helpers else empty)
        ^^ (if !emit_generic_sail_int_helpers then generic_sail_int_helpers else empty)
      in
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
        ksprintf string "#ifndef %s\n#define %s\ntypedef struct { uint8_t bytes[%d]; } %s;\n#endif" guard guard
          length ctyp
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
        base_helpers
        ^^ (if !emit_generic_sail_int_helpers then generic_helpers else empty)
        ^^ native_signed_index_helpers ^^ native_unsigned_index_helpers ^^ native_init_helpers
      in
      [TypeDeclaration typedef; StaticFunctionDefinition helpers]
    )

  let codegen_tup ctx ctyps =
    let id = mk_id ("tuple_" ^ string_of_ctyp (CT_tup ctyps)) in
    if IdSet.mem id !generated then []
    else (
      let _, fields =
        List.fold_left
          (fun (n, fields) ctyp -> (n + 1, Bindings.add (mk_id ("tup" ^ string_of_int n)) ctyp fields))
          (0, Bindings.empty) ctyps
      in
      generated := IdSet.add id !generated;
      codegen_type_def
        { ctx with records = Bindings.add id ([], fields) ctx.records }
        (CTD_struct (id, [], Bindings.bindings fields))
    )

  let codegen_list ctx ctyp =
    let open Printf in
    let id = mk_id (string_of_ctyp (CT_list ctyp)) in
    if IdSet.mem id !generated then []
    else (
      generated := IdSet.add id !generated;
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
  let codegen_vector ctx ctyp =
    let open Printf in
    let id = mk_id (string_of_ctyp (CT_vector ctyp)) in
    if IdSet.mem id !generated then []
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
          (ksprintf string "%s_%s(%s *rop, %s op, const %s n, %s elem)" name (sgen_id id) (sgen_id id)
             (sgen_id id) index_type (sgen_ctyp ctyp)
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
            (ksprintf string "fast_unsigned_vector_access_%s(%s *rop, %s op, uint64_t n)" (sgen_id id)
               (sgen_ctyp ctyp) (sgen_id id)
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
      generated := IdSet.add id !generated;
      [
        TypeDeclaration vector_typedef;
        StaticFunctionDefinition vector_decl;
        StaticFunctionDefinition vector_clear;
      ]
      @ ( if !emit_generic_sail_int_helpers then
            [StaticFunctionDefinition vector_init]
          else []
        )
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
      @ [
        StaticFunctionDefinition internal_vector_update;
        StaticFunctionDefinition internal_vector_init;
      ]
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
    | CDEF_val (id, _, arg_ctyps, ret_ctyp, _) ->
        if ctx_is_extern id ctx then []
        else if is_stack_ctyp ctx ret_ctyp then
          [
            FunctionDeclaration
              (string
                 (Printf.sprintf "%s %s(%s%s);" (sgen_ctyp ret_ctyp) (sgen_function_id id) (extra_params ())
                    (Util.string_of_list ", " sgen_const_ctyp arg_ctyps)
                 )
              );
          ]
        else
          [
            FunctionDeclaration
              (string
                 (Printf.sprintf "void %s(%s%s *rop, %s);" (sgen_function_id id) (extra_params ()) (sgen_ctyp ret_ctyp)
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

        [VariableDefinition variable_defs; FunctionDeclaration function_decls; FunctionDefinition impl]
    | CDEF_pragma _ -> []

  (** As we generate C we need to generate specialized version of tuple, list, and vector type. These must be generated
      in the correct order. The ctyp_dependencies function generates a list of c_gen_typs in the order they must be
      generated. Types may be repeated in ctyp_dependencies so it's up to the code-generator not to repeat definitions
      pointlessly (using the !generated variable) *)
  type c_gen_typ =
    | CTG_checked_native_int
    | CTG_u256
    | CTG_fixed_bytes of int
    | CTG_tup of ctyp list
    | CTG_list of ctyp
    | CTG_vector of ctyp

  let rec ctyp_dependencies = function
    | CT_fint _ | CT_fuint _ -> [CTG_checked_native_int]
    | ctyp when is_c_repr_u256 ctyp -> [CTG_u256]
    | ctyp when is_c_repr_fixed_bytes ctyp -> [CTG_fixed_bytes (Option.get (c_repr_fixed_bytes_length ctyp))]
    | CT_tup ctyps -> List.concat (List.map ctyp_dependencies ctyps) @ [CTG_tup ctyps]
    | CT_list ctyp -> ctyp_dependencies ctyp @ [CTG_list ctyp]
    | CT_vector ctyp | CT_fvector (_, ctyp) -> ctyp_dependencies ctyp @ [CTG_vector ctyp]
    | CT_ref ctyp -> ctyp_dependencies ctyp
    | CT_struct (_, ctyps) | CT_variant (_, ctyps) -> List.concat (List.map ctyp_dependencies ctyps)
    | CT_lint | CT_lbits | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_real | CT_string
    | CT_enum _ | CT_poly _ | CT_constant _ | CT_float _ | CT_rounding_mode | CT_memory_writes | CT_json | CT_json_key
      ->
        []

  (* Generate types and utility functions for non-bitvector vectors, tuples and lists.
     The functions are pure, and only emitted in the implementation file as static functions. *)
  let codegen_ctg ctx = function
    | CTG_checked_native_int -> codegen_checked_native_int ()
    | CTG_u256 -> codegen_u256 ()
    | CTG_fixed_bytes length -> codegen_fixed_bytes length
    | CTG_vector ctyp -> codegen_vector ctx ctyp
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
      let c_repr_uint64 = Config.c_repr_uint64
      let c_repr_int64 = Config.c_repr_int64
      let c_repr_u256 = Config.c_repr_u256
      let c_repr_fixed_bytes = Config.c_repr_fixed_bytes
      let specialize_c = Config.specialize_c
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

    let model_init =
      separate hardline
        (List.map string
           ([Printf.sprintf "void %smodel_init(void)" (class_impl_prefix ()); "{"; "  setup_rts();"]
           @ fst exn_boilerplate
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

    [FunctionDefinition model_init; FunctionDefinition model_fini]

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
      (match aux with
      | I_funcall (_, _, (callee, _), _) when Id.compare callee target = 0 -> found := true
      | _ -> ());
      funcall :: exception_instrs
    in
    ignore (cdef_map_funcall inspect cdef);
    !found

  let remove_uncalled_specialized_wrappers cdefs =
    let neq_int = mk_id "neq_int" in
    if Config.specialize_c && not (List.exists (cdef_calls neq_int) cdefs) then
      List.filter
        (function
          | CDEF_aux (CDEF_val (id, _, _, _, _), _) | CDEF_aux (CDEF_fundef (id, _, _, _), _)
            when Id.compare id neq_int = 0 ->
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
        (* Extern valspecs are retained in JIB for call typing, but codegen_def
           intentionally emits no declaration for them.  A real call still
           carries its argument/result types in an instruction and is counted. *)
        | CDEF_aux ((CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _)), _)
          when ctx_is_extern id ctx ->
            false
        | cdef -> cdef_has_ctyp (ctyp_contains pred) cdef
        )
      cdefs

  let compile_ast env effect_info basename ast =
    try
      let cdefs, ctx = jib_of_ast env effect_info ast in
      (* let cdefs', _ = Jib_optimize.remove_tuples cdefs ctx in *)
      let cdefs = insert_heap_returns ctx Bindings.empty cdefs in

      let recursive_functions = get_recursive_functions cdefs in
      let cdefs = optimize ~have_rts:(not Config.no_rts) ctx recursive_functions cdefs in

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
      emit_generic_sail_int_helpers := (not Config.specialize_c) || has_sail_int;
      emit_generic_lbits_helpers := (not Config.specialize_c) || has_lbits || has_sail_int;

      let docs = List.map (codegen_def ctx) cdefs |> List.concat in

      let docs = docs @ gen_model_init_fini ctx cdefs @ gen_unit_test_defs ctx cdefs in
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
          ((if Config.no_lib then []
            else [string "#include \"sail.h\""; string "#include \"sail_config.h\""; string "#include <string.h>"])
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

      (header, impl)
    with Type_error.Type_error (l, err) ->
      c_error ~loc:l ("Unexpected type error when compiling to C:\n" ^ fst (Type_error.string_of_type_error err))
end
