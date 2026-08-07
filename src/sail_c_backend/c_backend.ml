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
let optimize_stack_aggregates = ref false
let optimize_unit_results = ref false
let optimize_inline_attr = ref false

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
let c_repr_fixed_bytes_u64_lanes_id = mk_id "__sail_c_repr_fixed_bytes_u64_lanes"
let c_repr_byte_pointer_prefix = "__sail_c_repr_byte_pointer_"
let c_repr_const_byte_pointer_prefix = "__sail_c_repr_const_byte_pointer_"
let direct_byte_pointer_adapter = "__direct"
let c_repr_u128_ctyp = CT_struct (c_repr_u128_id, [])
let c_repr_u256_ctyp = CT_struct (c_repr_u256_id, [])
let c_repr_u320_ctyp = CT_struct (c_repr_u320_id, [])
let c_repr_fixed_bytes_ctyp n = CT_struct (c_repr_fixed_bytes_id, [CT_constant (Big_int.of_int n)])
let c_repr_fixed_bytes_u64_lanes_ctyp n = CT_struct (c_repr_fixed_bytes_u64_lanes_id, [CT_constant (Big_int.of_int n)])
let c_repr_byte_pointer_ctyp adapter = CT_struct (mk_id (c_repr_byte_pointer_prefix ^ adapter), [])
let c_repr_const_byte_pointer_ctyp adapter = CT_struct (mk_id (c_repr_const_byte_pointer_prefix ^ adapter), [])

let is_c_repr_u128 = function CT_struct (id, []) -> Id.compare id c_repr_u128_id = 0 | _ -> false

let is_c_repr_u256 = function CT_struct (id, []) -> Id.compare id c_repr_u256_id = 0 | _ -> false

let is_c_repr_u320 = function CT_struct (id, []) -> Id.compare id c_repr_u320_id = 0 | _ -> false

let c_repr_plain_fixed_bytes_length = function
  | CT_struct (id, [CT_constant n]) when Id.compare id c_repr_fixed_bytes_id = 0 -> (
      try Some (Big_int.to_int n) with _ -> None
    )
  | _ -> None

let c_repr_fixed_bytes_u64_lanes_length = function
  | CT_struct (id, [CT_constant n]) when Id.compare id c_repr_fixed_bytes_u64_lanes_id = 0 -> (
      try Some (Big_int.to_int n) with _ -> None
    )
  | _ -> None

let c_repr_fixed_bytes_length ctyp =
  match c_repr_plain_fixed_bytes_length ctyp with
  | Some _ as length -> length
  | None -> c_repr_fixed_bytes_u64_lanes_length ctyp

let is_c_repr_fixed_bytes_u64_lanes ctyp = Option.is_some (c_repr_fixed_bytes_u64_lanes_length ctyp)

let is_c_repr_fixed_bytes ctyp = Option.is_some (c_repr_fixed_bytes_length ctyp)

let c_repr_pointer_adapter prefix = function
  | CT_struct (id, []) ->
      let name = string_of_id id in
      if String.starts_with ~prefix name then
        Some (String.sub name (String.length prefix) (String.length name - String.length prefix))
      else None
  | _ -> None

let c_repr_mutable_byte_pointer_adapter ctyp = c_repr_pointer_adapter c_repr_byte_pointer_prefix ctyp

let c_repr_const_byte_pointer_adapter ctyp = c_repr_pointer_adapter c_repr_const_byte_pointer_prefix ctyp

let c_repr_byte_pointer_adapter ctyp =
  match c_repr_mutable_byte_pointer_adapter ctyp with
  | Some _ as adapter -> adapter
  | None -> c_repr_const_byte_pointer_adapter ctyp

let is_c_repr_const_byte_pointer ctyp = Option.is_some (c_repr_const_byte_pointer_adapter ctyp)

let is_c_repr_byte_pointer ctyp = Option.is_some (c_repr_byte_pointer_adapter ctyp)

let is_c_repr_value ctyp =
  is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp || is_c_repr_fixed_bytes ctyp
  || is_c_repr_byte_pointer ctyp

(* A [$[c_repr {representation = external, ...}]] struct delegates its
   complete layout and value semantics to a concrete C declaration.  Its Sail
   definition may intentionally contain managed fields that do not exist in
   that ABI (for example, a semantic list represented by a cursor).  Treat
   these named representations as C values throughout JIB lowering; otherwise
   locals and call results incorrectly acquire CREATE/KILL ownership calls for
   the hidden Sail fields.  This set is reset for every C compilation below. *)
let c_repr_external_value_types = ref IdSet.empty

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
  | CT_struct (id, []) when IdSet.mem id !c_repr_external_value_types -> true
  | CT_fbits _ | CT_sbits _ | CT_unit | CT_bool | CT_enum _ -> true
  | CT_fint n -> n <= 128
  | CT_fuint n -> n <= 64
  | CT_lint when !optimize_fixed_int -> true
  | CT_lint -> false
  | CT_lbits when !optimize_fixed_bits -> true
  | CT_lbits -> false
  | CT_real | CT_string | CT_list _ | CT_vector _ -> false
  | CT_fvector (_, ctyp) -> !optimize_stack_aggregates && is_stack_ctyp ctx ctyp
  | CT_struct (_, _) ->
      let _, fields = struct_field_bindings Parse_ast.Unknown ctx ctyp in
      Bindings.for_all (fun _ ctyp -> is_stack_ctyp ctx ctyp) fields
  | CT_variant _ as ctyp when !optimize_stack_aggregates ->
      let _, constructors = variant_constructor_bindings Parse_ast.Unknown ctx ctyp in
      Bindings.for_all (fun _ ctyp -> is_stack_ctyp ctx ctyp) constructors
  | CT_variant _ -> false
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

let c_case_block ~case_break b =
  let terminator = if case_break then [c_stmt "break"] else [] in
  nest 2 (separate hardline ([lbrace] @ b @ terminator)) ^^ hardline ^^ rbrace

(* Generate a C switch statement. If default is true, then we generate a `default: break;` case at the end. *)
let c_switch ?(default = false) ?(case_break = true) cond cases =
  match cases with
  | [] -> string "{}"
  | _ ->
      string "switch" ^^ space ^^ cond ^^ space ^^ lbrace ^^ hardline
      ^^ separate_map hardline
           (fun (case_exp, case_block) ->
             string "case" ^^ space ^^ case_exp ^^ colon
             ^^ if case_block = [] && not case_break then empty else space ^^ c_case_block ~case_break case_block
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
  val c_repr_fixed_bytes_u64_lanes : int Bindings.t
  val c_repr_fixed_bytes_u64_lane_alias_lengths : int list
  val byte_pointer_fields : (id * id * string) list
  val byte_pointer_types : string Bindings.t
  val byte_pointer_signatures : (string option list * string option) Bindings.t
  val fixed_bytes_signatures : (int option list * int option) Bindings.t
  val fixed_bytes_u64_lanes_signatures : (int option list * int option) Bindings.t
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

  let rec find_c_repr_fixed_bytes_u64_lanes env (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_id id -> (
        match Bindings.find_opt id Opts.c_repr_fixed_bytes_u64_lanes with
        | Some length -> Some length
        | None -> (
            match Bindings.find_opt id (Env.get_typ_synonyms env) with
            | Some ([], A_aux (A_typ typ, _)) -> find_c_repr_fixed_bytes_u64_lanes env typ
            | _ -> None
          )
      )
    | _ -> None

  let rec find_c_repr_byte_pointer env (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_id id -> (
        match Bindings.find_opt id Opts.byte_pointer_types with
        | Some adapter -> Some adapter
        | None -> (
            match Bindings.find_opt id (Env.get_typ_synonyms env) with
            | Some ([], A_aux (A_typ typ, _)) -> find_c_repr_byte_pointer env typ
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
      match Bindings.find_opt id Opts.c_repr_fixed_bytes_u64_lanes with
      | Some length when Opts.specialize_c -> c_repr_fixed_bytes_u64_lanes_ctyp length
      | _ -> (
          match Bindings.find_opt id Opts.c_repr_fixed_bytes with
          | Some length when Opts.specialize_c -> c_repr_fixed_bytes_ctyp length
          | _ -> (
              match ctyp with
              | CT_fvector (length, CT_fbits 8) when Opts.specialize_c && length > 0 -> c_repr_fixed_bytes_ctyp length
              | _ -> ctyp
            )
        )
    )

  let specialize_struct_field record_id field_id ctyp =
    match
      List.find_opt
        (fun (configured_record, configured_field, _) ->
          Id.compare record_id configured_record = 0 && Id.compare field_id configured_field = 0
        )
        Opts.byte_pointer_fields
    with
    | Some (_, _, adapter) when Opts.optimized_model -> c_repr_const_byte_pointer_ctyp adapter
    | Some _ | None -> ctyp

  let specialize_declared_function_argument function_id index ctyp =
    match Bindings.find_opt function_id Opts.fixed_bytes_u64_lanes_signatures with
    | Some (arguments, _) -> (
        match List.nth_opt arguments index with
        | Some (Some length) when Opts.specialize_c -> c_repr_fixed_bytes_u64_lanes_ctyp length
        | Some (Some _) | Some None | None -> ctyp
      )
    | None -> (
        match Bindings.find_opt function_id Opts.fixed_bytes_signatures with
        | Some (arguments, _) -> (
            match List.nth_opt arguments index with
            | Some (Some length) when Opts.specialize_c -> c_repr_fixed_bytes_ctyp length
            | Some (Some _) | Some None | None -> ctyp
          )
        | None -> (
            match Bindings.find_opt function_id Opts.byte_pointer_signatures with
            | Some (arguments, _) -> (
                match List.nth_opt arguments index with
                | Some (Some adapter) when Opts.optimized_model -> c_repr_byte_pointer_ctyp adapter
                | Some (Some _) | Some None | None -> ctyp
              )
            | None -> ctyp
          )
      )

  let specialize_declared_function_result function_id ctyp =
    match Bindings.find_opt function_id Opts.fixed_bytes_u64_lanes_signatures with
    | Some (_, Some length) when Opts.specialize_c -> c_repr_fixed_bytes_u64_lanes_ctyp length
    | Some (_, Some _) | Some (_, None) -> ctyp
    | None -> (
        match Bindings.find_opt function_id Opts.fixed_bytes_signatures with
        | Some (_, Some length) when Opts.specialize_c -> c_repr_fixed_bytes_ctyp length
        | Some (_, Some _) | Some (_, None) -> ctyp
        | None -> (
            match Bindings.find_opt function_id Opts.byte_pointer_signatures with
            | Some (_, Some adapter) when Opts.optimized_model -> c_repr_byte_pointer_ctyp adapter
            | Some (_, Some _) | Some (_, None) | None -> ctyp
          )
      )

  let specializes_narrow_fixed_integer ~semantic ~represented =
    match (semantic, represented) with
    | (CT_fint semantic_width | CT_fuint semantic_width), (CT_fint represented_width | CT_fuint represented_width) ->
        represented_width < semantic_width
    | _ -> false

  let rec representation_refines ~semantic ~represented =
    match (semantic, represented) with
    | (CT_lint | CT_fint _ | CT_fuint _ | CT_constant _), represented when is_c_repr_byte_pointer represented -> true
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

  let propagate_anf_temporary_representation ~semantic ~represented =
    representation_refines ~semantic ~represented && is_c_repr_byte_pointer represented

  (* The Sail typechecker has already proved the actual argument inhabits the
     semantic parameter type.  When its selected fixed representation is
     strictly narrower, retain it by cloning the local function instead of
     inserting a widening conversion at the call boundary. *)
  let specialize_function_argument_representation ~semantic ~represented =
    Opts.specialize_c
    && (specializes_narrow_fixed_integer ~semantic ~represented
       ||
       match (semantic, represented) with
       | (CT_lint | CT_fint _ | CT_fuint _ | CT_constant _), represented when is_c_repr_byte_pointer represented -> true
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
       | (CT_lint | CT_fint _ | CT_fuint _ | CT_constant _), represented when is_c_repr_byte_pointer represented -> true
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
    | _, (CT_lint | CT_fint _ | CT_fuint _ | CT_constant _), represented, _ when is_c_repr_byte_pointer represented ->
        Some expected
    | _ -> None

  let function_argument_narrowing_allowed ~expected ~source:_ ~represented =
    ((is_c_repr_u128 expected || is_c_repr_u256 expected || is_c_repr_u320 expected) && ctyp_equal represented CT_lint)
    ||
    match expected with
    | CT_fuint _ -> is_c_repr_u128 represented || is_c_repr_u256 represented || is_c_repr_u320 represented
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
    | (CT_fint semantic_width | CT_fuint semantic_width), (CT_fint represented_width | CT_fuint represented_width) ->
        semantic_width = represented_width
    | semantic, represented
      when (is_c_repr_u128 semantic && (is_c_repr_u256 represented || is_c_repr_u320 represented))
           || (is_c_repr_u256 semantic && is_c_repr_u320 represented) ->
        true
    | _ -> false

  let preserve_aval_representation ~semantic ~represented =
    match semantic with
    | (CT_lint | CT_fint _ | CT_fuint _ | CT_constant _) when is_c_repr_byte_pointer represented -> true
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
    match Bindings.find_opt id Opts.c_repr_fixed_bytes_u64_lanes with
    | Some length when Opts.specialize_c -> ctyp_equal represented (c_repr_fixed_bytes_u64_lanes_ctyp length)
    | _ -> (
        match Bindings.find_opt id Opts.c_repr_fixed_bytes with
        | Some length when Opts.specialize_c -> ctyp_equal represented (c_repr_fixed_bytes_ctyp length)
        | _ -> false
      )

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
    let declared = specialize_declared_function_result id semantic in
    if not (ctyp_equal declared semantic) then declared
    else (
      match (string_of_id id, arg_ctyps, semantic) with
      | "add_int", [pointer; (CT_fint _ | CT_fuint _ | CT_constant _)], _ when is_c_repr_byte_pointer pointer -> pointer
      | "add_int", [(CT_fint _ | CT_fuint _ | CT_constant _); pointer], _ when is_c_repr_byte_pointer pointer -> pointer
      | "from_bytes_le", [(CT_fint _ | CT_fuint _); bytes], CT_lbits when fixed_bytes_at_most_32 bytes ->
          c_repr_u256_ctyp
      | _ -> (
          match (preserves_first_argument, arg_ctyps) with
          | true, represented :: _ when representation_refines ~semantic ~represented -> represented
          | _ -> semantic
        )
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
    | _, _, _, (CT_lint | CT_fint _ | CT_fuint _ | CT_constant _), represented when is_c_repr_byte_pointer represented
      ->
        true
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
    let c_repr_fixed_bytes_u64_lanes = find_c_repr_fixed_bytes_u64_lanes ctx.local_env typ in
    let c_repr_byte_pointer = find_c_repr_byte_pointer ctx.local_env typ in
    let (Typ_aux (typ_aux, l) as typ) = Env.expand_synonyms ctx.local_env typ in
    match typ_aux with
    | _ when Option.is_some c_repr_unsigned -> CT_fuint (Option.get c_repr_unsigned)
    | _ when Option.is_some c_repr_signed -> CT_fint (Option.get c_repr_signed)
    | _ when c_repr_u256 -> c_repr_u256_ctyp
    | _ when Option.is_some c_repr_fixed_bytes_u64_lanes ->
        c_repr_fixed_bytes_u64_lanes_ctyp (Option.get c_repr_fixed_bytes_u64_lanes)
    | _ when Option.is_some c_repr_fixed_bytes -> c_repr_fixed_bytes_ctyp (Option.get c_repr_fixed_bytes)
    | _ when Option.is_some c_repr_byte_pointer -> c_repr_byte_pointer_ctyp (Option.get c_repr_byte_pointer)
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
            try
              let length = Big_int.to_int length in
              if List.mem length Opts.c_repr_fixed_bytes_u64_lane_alias_lengths then
                c_repr_fixed_bytes_u64_lanes_ctyp length
              else c_repr_fixed_bytes_ctyp length
            with _ -> CT_vector elem_ctyp
          )
        | Nexp_aux (Nexp_constant length, _) when Opts.specialize_c && Big_int.less_equal (Big_int.of_int 1) length -> (
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
    | AV_cval (V_field (record, field, _), typ) -> (
        match cval_ctyp record with
        | CT_struct _ as record_ctyp ->
            let _, field_ctyp = struct_fields (id_loc field) ctx record_ctyp in
            AV_cval (V_field (record, field, field_ctyp field), typ)
        | _ -> AV_cval (V_field (record, field, convert_typ ctx typ), typ)
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
        match cval_ctyp value with CT_fbits width -> Some { origin_value = value; origin_width = width } | _ -> None
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
    | AE_let (mut, id, _, binding, body, _) -> (
        match (mut, conversion_result_origin conversion_origins binding) with
        | Immutable, Some origin -> conversion_result_origin (NameMap.add id origin conversion_origins) body
        | Mutable, _ | Immutable, None -> None
      )
    | _ -> None

  let aexp_uses_name id aexp =
    (* [optimize_anf] runs after [no_shadow], so equality of ANF names is enough
       to decide whether the rewritten body still refers to this binding. *)
    let used = ref false in
    let check_cval cval =
      Jib_util.map_cval
        (function
          | V_id (used_id, _) as cval when Name.compare used_id id = 0 ->
              used := true;
              cval
          | cval -> cval
          )
        cval
    in
    ignore
      (Anf.map_aval
         (fun _ -> function
           | AV_id (used_id, _) as aval when Name.compare used_id id = 0 ->
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
      | AE_short_circuit (op, aval, aexp) -> AE_short_circuit (op, aval, analyze_functions ctx conversion_origins f aexp)
      | AE_let (mut, id, typ1, aexp1, (AE_aux (_, { env = env2; _ }) as aexp2), typ2) -> (
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
            match mut with Immutable -> conversion_result_origin conversion_origins aexp1 | Mutable -> None
          in
          let conversion_origins =
            match binding_origin with
            | Some origin -> NameMap.add id origin conversion_origins
            | None -> NameMap.remove id conversion_origins
          in
          let aexp2 = analyze_functions ctx conversion_origins f aexp2 in
          match binding_origin with
          | Some _ when not (aexp_uses_name id aexp2) ->
              let (AE_aux (aexp2, _)) = aexp2 in
              aexp2
          | Some _ | None -> AE_let (mut, id, typ1, aexp1, aexp2, typ2)
        )
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
    let semantic_index_in_bounds length aval =
      match semantic_integer_bounds aval with
      | Some (env, lower, upper) ->
          prove __POS__ env (nc_lteq (nconstant Big_int.zero) lower)
          && prove __POS__ env (nc_lt upper (nconstant (Big_int.of_int length)))
      | None -> false
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
    | "not", [AV_cval (value, _)] when ctyp_equal (cval_ctyp value) CT_bool ->
        AE_val (AV_cval (V_call (Bnot, [value]), typ))
    | ("eq_bool" | "eq_anything"), [AV_cval (left, _); AV_cval (right, _)]
      when ctyp_equal (cval_ctyp left) CT_bool && ctyp_equal (cval_ctyp right) CT_bool ->
        AE_val (AV_cval (V_call (Eq, [left; right]), typ))
    | "eq_anything", [AV_cval (left, _); AV_cval (right, _)]
      when ctyp_equal (cval_ctyp left) (cval_ctyp right) && is_c_repr_value (cval_ctyp left) ->
        (* Representation-specialized scalar values have ordinary pure C
           equality helpers.  Keep their equality in cval form so later
           copy propagation can use it directly in a branch or return,
           instead of forcing a named boolean function-call destination. *)
        AE_val (AV_cval (V_call (Eq, [left; right]), typ))
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
    | "eq_int", [AV_cval (v1, _); AV_cval (v2, _)]
      when is_c_repr_byte_pointer (cval_ctyp v1) && ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Eq, [v1; v2]), typ))
    | "neq_int", [AV_cval (v1, _); AV_cval (v2, _)]
      when is_c_repr_byte_pointer (cval_ctyp v1) && ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        AE_val (AV_cval (V_call (Neq, [v1; v2]), typ))
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
        | Some (Nexp_aux (Nexp_constant source_width, _)), Some (Nexp_aux (Nexp_constant target_width, _))
          when Big_int.less_equal source_width (Big_int.of_int 64) && Big_int.less_equal target_width (Big_int.of_int 64)
          -> (
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
        | Some (Nexp_aux (Nexp_constant source_width, _)), Some (Nexp_aux (Nexp_constant target_width, _))
          when Big_int.less_equal source_width (Big_int.of_int 64) && Big_int.less_equal target_width (Big_int.of_int 64)
          -> (
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
        | Some (Nexp_aux (Nexp_constant source_width, _)), Some (Nexp_aux (Nexp_constant target_width, _))
          when Big_int.less_equal source_width (Big_int.of_int 64) && Big_int.less_equal target_width (Big_int.of_int 64)
          -> (
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
    | (("lteq" | "gteq" | "lt" | "gt") as comparison), [AV_cval (v1, _); AV_cval (v2, _)]
      when is_c_repr_byte_pointer (cval_ctyp v1) && ctyp_equal (cval_ctyp v1) (cval_ctyp v2) ->
        let op =
          match comparison with "lteq" -> Ilteq | "gteq" -> Igteq | "lt" -> Ilt | "gt" -> Igt | _ -> assert false
        in
        AE_val (AV_cval (V_call (op, [v1; v2]), typ))
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
        | CT_fbits result_width, CT_fbits source_width, CT_fbits slice_width when result_width = source_width -> (
            let position_is_proven =
              match semantic_args with
              | [_; _; _; semantic_start; _] ->
                  Option.is_some
                    (Jib_semantics.prove_bit_insert_position_bounds ~env:ctx.local_env ~index:3
                       ~typ:(aval_typ semantic_start) ~interval:None ~carrier_width:result_width
                       ~inserted_width:slice_width
                    )
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
      when Opts.specialize_c
           &&
           match (cval_ctyp vec, semantic_args) with
           | CT_fvector (length, element_ctyp), [_; semantic_index]
             when is_stack_ctyp ctx element_ctyp && semantic_index_in_bounds length semantic_index ->
               true
           | _ -> false -> (
        match cval_ctyp vec with
        | CT_fvector (length, _) -> AE_val (AV_cval (V_call (Proven_vector_access length, [vec; n]), typ))
        | _ -> assert false
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
    | "add_int", [AV_cval (pointer, _); AV_cval (offset, _)]
      when is_c_repr_byte_pointer (cval_ctyp pointer)
           && match cval_ctyp offset with CT_fint _ | CT_fuint _ | CT_constant _ -> true | _ -> false ->
        AE_val (AV_cval (V_call (Iadd, [pointer; offset]), typ))
    | "add_int", [AV_cval (offset, _); AV_cval (pointer, _)]
      when is_c_repr_byte_pointer (cval_ctyp pointer)
           && match cval_ctyp offset with CT_fint _ | CT_fuint _ | CT_constant _ -> true | _ -> false ->
        AE_val (AV_cval (V_call (Iadd, [pointer; offset]), typ))
    | "sub_int", [AV_cval (left, _); AV_cval (right, _)]
      when is_c_repr_byte_pointer (cval_ctyp left) && ctyp_equal (cval_ctyp left) (cval_ctyp right) ->
        AE_app (Pure_extern (mk_id "__sail_byte_pointer_diff", Some typ), args, typ)
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
          when semantic_integer_nonnegative left && semantic_integer_nonnegative right
               && proven_native_op represented Idiv ->
            (* Euclidean and truncating division coincide for non-negative
               operands.  Emit the proof-bearing marker while the source
               environment still knows that the divisor is non-zero (for
               example after a terminating zero guard); later graph
               specialization can then keep the operation native. *)
            AE_app (Pure_extern (mk_id (proven_marker Idiv), Some typ), args, typ)
        | _ -> native_integer_binary_or_no_change Idiv op1 op2
      )
    | "emod_int", [AV_cval (op1, _); AV_cval (op2, _)] -> (
        let nonnegative_dividend =
          match cval_ctyp op1 with
          | CT_fuint _ -> true
          | ctyp when is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp -> true
          | CT_constant value -> Big_int.less_equal Big_int.zero value
          | _ -> false
        in
        let represented = convert_typ ctx typ in
        match semantic_args with
        | [left; right]
          when semantic_integer_nonnegative left && semantic_integer_nonnegative right
               && proven_native_op represented Imod ->
            AE_app (Pure_extern (mk_id (proven_marker Imod), Some typ), args, typ)
        | _ -> if nonnegative_dividend then native_integer_binary_or_no_change Imod op1 op2 else no_change
      )
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
        if !optimize_primops then (try analyze_primop' ctx conversion_origins id args typ with Failure _ -> no_change)
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

(* == --c-inline-attr ======================================================
   Calls to functions carrying the $[c_inline] attribute are inlined into
   their callers with the generic JIB inliner.  This MUST run before
   [insert_heap_returns]: the inliner substitutes the canonical JIB return
   protocol (writes to the [return] name followed by [I_end]/[I_undefined]),
   which insert_heap_returns rewrites into [I_return]/heap-return pointers
   that [Jib_optimize.inline] does not understand.  Exception control flow
   is already lowered by this point (jib_compile's fix_exception), so an
   inlined body's exception exits fall through to the caller's existing
   have_exception check after its call site.

   The attribute is read from the CDEF_fundef def_annot, so specialized
   clones (which share the annotated definition's def_annot) inline exactly
   like their source function.  Marked functions are still emitted as
   ordinary definitions; only their call sites change.

   The inliner freshens labels but not declared locals, so a caller and an
   inlined body may declare the same source-named local.  The later custom
   copy/alias passes assume declaration names are unique per function body,
   so [uniquify_inlined_declarations] re-runs the compile-time uniquing over
   the merged body. *)
let c_inline_attribute = "c_inline"

let has_c_inline_attribute def_annot = Option.is_some (get_def_attribute c_inline_attribute def_annot)

(* Copy $[c_inline] from val specs onto their function definitions: the
   optimized model attaches the attribute through attribute-only val splices,
   and jib_compile builds each CDEF_fundef def_annot from the DEF_fundef. *)
let propagate_inline_attributes ast =
  let open Ast_defs in
  let annotated_specs =
    List.fold_left
      (fun ids (DEF_aux (def, def_annot)) ->
        match def with
        | DEF_val (VS_aux (VS_val_spec (_, id, _), _)) when has_c_inline_attribute def_annot -> IdSet.add id ids
        | _ -> ids
      )
      IdSet.empty ast.defs
  in
  if IdSet.is_empty annotated_specs then ast
  else
    {
      ast with
      defs =
        List.map
          (fun (DEF_aux (def, def_annot) as full_def) ->
            match def with
            | DEF_fundef fd when IdSet.mem (id_of_fundef fd) annotated_specs && not (has_c_inline_attribute def_annot)
              ->
                DEF_aux (def, add_def_attribute (gen_loc def_annot.loc) c_inline_attribute None def_annot)
            | _ -> full_def
          )
          ast.defs;
    }

let uniquify_inlined_declarations instrs =
  let unique_id ctyp = function
    | Name (id, _) -> ngensym ~source_name:(string_of_id id) ~source_type:(string_of_ctyp ctyp) ()
    | Gen (_, _, _, source_name, source_type) -> ngensym ?source_name ?source_type ()
    | _ -> ngensym ~source_name:"value" ~source_type:(string_of_ctyp ctyp) ()
  in
  let rec go seen = function
    | I_aux (I_decl (ctyp, id), aux) :: instrs when NameSet.mem id seen ->
        let id' = unique_id ctyp id in
        let instrs', seen = go seen instrs in
        (I_aux (I_decl (ctyp, id'), aux) :: instrs_rename id id' instrs', seen)
    | I_aux (I_decl (ctyp, id), aux) :: instrs ->
        let instrs', seen = go (NameSet.add id seen) instrs in
        (I_aux (I_decl (ctyp, id), aux) :: instrs', seen)
    | I_aux (I_init (ctyp, id, init), aux) :: instrs when NameSet.mem id seen ->
        let id' = unique_id ctyp id in
        let instrs', seen = go seen instrs in
        (I_aux (I_init (ctyp, id', init), aux) :: instrs_rename id id' instrs', seen)
    | I_aux (I_init (ctyp, id, init), aux) :: instrs ->
        let instrs', seen = go (NameSet.add id seen) instrs in
        (I_aux (I_init (ctyp, id, init), aux) :: instrs', seen)
    | I_aux (I_block block, aux) :: instrs ->
        let block', seen = go seen block in
        let instrs', seen = go seen instrs in
        (I_aux (I_block block', aux) :: instrs', seen)
    | I_aux (I_try_block block, aux) :: instrs ->
        let block', seen = go seen block in
        let instrs', seen = go seen instrs in
        (I_aux (I_try_block block', aux) :: instrs', seen)
    | I_aux (I_if (cval, then_instrs, else_instrs), aux) :: instrs ->
        let then_instrs', seen = go seen then_instrs in
        let else_instrs', seen = go seen else_instrs in
        let instrs', seen = go seen instrs in
        (I_aux (I_if (cval, then_instrs', else_instrs'), aux) :: instrs', seen)
    | instr :: instrs ->
        let instrs', seen = go seen instrs in
        (instr :: instrs', seen)
    | [] -> ([], seen)
  in
  fst (go NameSet.empty instrs)

let inline_marked_functions cdefs =
  let marked =
    List.fold_left
      (fun marked -> function
        | CDEF_aux (CDEF_fundef (id, Return_plain, _, _), def_annot) when has_c_inline_attribute def_annot ->
            IdSet.add id marked
        | _ -> marked
        )
      IdSet.empty cdefs
  in
  if IdSet.is_empty marked then cdefs
  else (
    let direct_marked_calls body =
      List.fold_left
        (fun calls instr ->
          let found = ref calls in
          iter_instr
            (function
              | I_aux (I_funcall (_, Call _, (fid, _), _), _) when IdSet.mem fid marked ->
                  found := IdSet.add fid !found
              | _ -> ()
              )
            instr;
          !found
        )
        IdSet.empty body
    in
    let marked_edges =
      List.fold_left
        (fun edges -> function
          | CDEF_aux (CDEF_fundef (id, Return_plain, _, body), _) when IdSet.mem id marked ->
              Bindings.add id (direct_marked_calls body) edges
          | _ -> edges
          )
        Bindings.empty cdefs
    in
    (* Reject marked cycles up front: the fixpoint inliner would re-expand a
       recursive marked call forever. *)
    let rec closure acc frontier =
      if IdSet.is_empty frontier then acc
      else (
        let next =
          IdSet.fold
            (fun id next ->
              match Bindings.find_opt id marked_edges with
              | Some callees -> IdSet.union callees next
              | None -> next
            )
            frontier IdSet.empty
        in
        let fresh = IdSet.diff next acc in
        closure (IdSet.union acc fresh) fresh
      )
    in
    IdSet.iter
      (fun id ->
        let callees = Option.value ~default:IdSet.empty (Bindings.find_opt id marked_edges) in
        if IdSet.mem id (closure callees callees) then
          c_error ~loc:(id_loc id) ("$[c_inline] function " ^ string_of_id id ^ " is (mutually) recursive")
      )
      marked;
    List.map
      (function
        | CDEF_aux (CDEF_fundef (id, heap_return, args, body), def_annot)
          when (not (IdSet.mem id marked)) && not (IdSet.is_empty (direct_marked_calls body)) ->
            let body = Jib_optimize.inline cdefs (fun call -> IdSet.mem call marked) body in
            let body = uniquify_inlined_declarations body in
            CDEF_aux (CDEF_fundef (id, heap_return, args, body), def_annot)
        | cdef -> cdef
        )
      cdefs
  )

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
                  (I_if (condition, rewrite literal_environment then_body, rewrite literal_environment else_body), aux)
            | instr -> instr
          in
          let literal_environment =
            match instr with
            | I_aux (I_copy (CL_id (name, _), (V_lit _ as literal)), _) -> NameMap.add name literal literal_environment
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
      | Some value when Big_int.less_equal Big_int.zero value && Big_int.less_equal value (Big_int.of_int Stdlib.max_int)
        ->
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
            | I_copy (CL_id (name, _), (V_lit _ as literal)) -> NameMap.add name (index, literal) definitions
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
            | I_copy (CL_id (name, _), V_call (((Bvshiftr | Proven_bvshiftr _) as op), [source; amount])) ->
                NameMap.add name (index, op, source, amount) definitions
            | _ -> definitions
          in
          (index + 1, definitions)
        )
        (0, NameMap.empty) instructions
      |> snd
    in
    let owns_lifecycle name = function
      | I_aux ((I_decl (_, candidate) | I_reset (_, candidate) | I_clear (_, candidate) | I_init (_, candidate, _)), _)
        ->
          Name.compare name candidate = 0
      | _ -> false
    in
    let private_temporary name definition_index use_index =
      let rec loop index =
        if index = count then true
        else (
          let instr = instructions.(index) in
          let allowed =
            index = definition_index || index = use_index || owns_lifecycle name instr
            || not (NameSet.mem name (instr_ids ~direct:false instr))
          in
          allowed && loop (index + 1)
        )
      in
      loop 0
    in
    let source_is_stable source first last =
      match source with
      | V_id (source_name, _) ->
          let rec loop index =
            index >= last
            || ((not (NameSet.mem source_name (instr_writes ~direct:false instructions.(index)))) && loop (index + 1))
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
              | Some literal when ctyp_equal ctyp (cval_ctyp literal) && source_is_stable value (-1) use_index ->
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
                 && source_is_stable source definition_index use_index ->
              let proven =
                match op with
                | Proven_bvshiftr 64 -> true
                | Bvshiftr -> (
                    match literal_value amount with
                    | Some amount ->
                        let interval = Some (amount, amount) in
                        Option.is_some (Jib_semantics.prove_shift_count_interval ~index:1 ~interval ~carrier_width:64)
                    | None -> false
                  )
                | Proven_bvshiftr _ | _ -> false
              in
              if proven then Some (name, definition_index, source, amount) else None
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
                  Option.bind shift (fun shift -> Option.map (fun literal -> (shift, mask, literal)) literal)
                )
                [(left, right); (right, left)]
            in
            match web with
            | Some ((shift_name, shift_index, source, amount), mask, (mask_definition, mask_value)) -> (
                match (cval_ctyp source, clexp_ctyp destination) with
                | CT_fbits source_width, CT_fbits result_width
                  when 0 < source_width && source_width <= 64 && source_width = result_width
                       && ctyp_equal (cval_ctyp mask) (CT_fbits result_width) -> (
                    match Jib_semantics.prove_low_mask_width ~carrier_width:result_width ~mask:mask_value with
                    | Some slice_width when slice_width <= source_width ->
                        let slice = V_call (Proven_slice (slice_width, 64), [source; amount]) in
                        let extracted =
                          if slice_width = result_width then slice else V_call (Zero_extend result_width, [slice])
                        in
                        Hashtbl.replace replacements mask_index (I_aux (I_copy (destination, extracted), aux));
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
            | I_aux ((I_decl (_, name) | I_reset (_, name) | I_clear (_, name) | I_init (_, name, _)), _)
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

(* A call whose stack-typed destination is never read disappears when Sail's
   effect analysis proves the callee pure; otherwise it becomes a bare call
   and the destination's declaration disappears. This keeps generated C free
   of `word tmp = f(...);` ceremony without discarding observable effects.
   Pure same-representation writes to unread stack locals disappear as well.
   Representation-changing writes are retained because their generated
   conversion may include a runtime domain check. Only local [Name]
   destinations proven unread across the whole body are rewritten. *)
let discard_unread_stack_results ctx (CDEF_aux (aux, def_annot)) =
  let effect_source id =
    List.find_map
      (fun (trace : Jib_compile.representation_specialization) ->
        if Id.compare trace.specialized_id id = 0 then Some trace.source_id else None
      )
      !Jib_compile.representation_specializations
    |> Option.value ~default:id
  in
  let call_is_pure (id, _) =
    (* The assertion marker lowers to a trap even though its source-level
       predicate computation is otherwise pure.  Its unit result may be
       unread, but the check itself is observable and must never disappear. *)
    let external_name = if ctx_is_extern id ctx then ctx_get_extern id ctx else string_of_id id in
    (not (String.equal external_name "__sail_fixed_assert" || String.equal external_name "fatal_error"))
    && Effects.function_is_pure (effect_source id) ctx.effect_info
  in
  let rewrite_body id body =
    let locals = ref NameSet.empty in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               (match aux with I_decl (_, name) | I_init (_, name, _) -> locals := NameSet.add name !locals | _ -> ());
               sub
             )
             instr
          )
      )
      body;
    let reads =
      List.fold_left (fun acc instr -> NameSet.union acc (instr_reads ~direct:false instr)) NameSet.empty body
    in
    let unread name = NameSet.mem name !locals && not (NameSet.mem name reads) in
    let keep_funcall = function
      | I_aux (I_funcall (CR_one (CL_id (name, ctyp)), _, callee, _), _)
        when is_stack_ctyp ctx ctyp && unread name && call_is_pure callee ->
          false
      | _ -> true
    in
    let body = filter_instrs keep_funcall body in
    let rewrite_funcall = function
      | I_aux (I_funcall (CR_one (CL_id (name, ctyp)), extern, f, args), annot)
        when is_stack_ctyp ctx ctyp && unread name ->
          I_aux (I_funcall (CR_one (CL_void ctyp), extern, f, args), annot)
      | instr -> instr
    in
    let body = List.map (map_instr rewrite_funcall) body in
    let keep_unread_stack_write = function
      | I_aux (I_copy (CL_id (name, ctyp), value), _)
        when is_stack_ctyp ctx ctyp && unread name && ctyp_equal ctyp (cval_ctyp value) ->
          false
      | I_aux (I_init (ctyp, name, Init_cval value), _)
        when is_stack_ctyp ctx ctyp && unread name && ctyp_equal ctyp (cval_ctyp value) ->
          false
      | I_aux (I_reinit (ctyp, name, value), _)
        when is_stack_ctyp ctx ctyp && unread name && ctyp_equal ctyp (cval_ctyp value) ->
          false
      | _ -> true
    in
    let body = filter_instrs keep_unread_stack_write body in
    let still_written = ref NameSet.empty in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               ( match aux with
               | I_decl _ -> ()
               | _ -> still_written := NameSet.union !still_written (instr_writes ~direct:true sub)
               );
               sub
             )
             instr
          )
      )
      body;
    let keep = function
      | I_aux (I_decl (ctyp, ((Name _ | Gen _) as name)), _) when is_stack_ctyp ctx ctyp ->
          NameSet.mem name reads || NameSet.mem name !still_written
      | _ -> true
    in
    filter_instrs keep body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body id body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Unit has exactly one semantic value, so an optimized C function never needs
   to materialize or pass it.  Keep CT_unit in JIB as the proof-facing type and
   erase only its administrative value flow immediately before C emission:

     - replace every pure unit-valued read with the unique unit literal;
     - remove standalone unit storage and assignments;
     - remove unit call arguments while retaining the call itself.

   Function signatures and unit returns are rendered as C void by Codegen.
   Unit payloads inside records/variants deliberately remain represented: this
   pass erases only values that have no enclosing data representation. *)
let is_variant_constructor ctx id =
  Bindings.exists (fun _ (_, constructors) -> Bindings.mem id constructors) ctx.variants

let erase_unit_scaffolding ctx (CDEF_aux (aux, def_annot)) =
  let erase_body body =
    let unique_unit value = if ctyp_equal (cval_ctyp value) CT_unit then V_lit (VL_unit, CT_unit) else value in
    let rewrite_call = function
      | I_aux (I_funcall (destination, extern, callee, args), annot) ->
          let args =
            if is_variant_constructor ctx (fst callee) then args
            else List.filter (fun arg -> not (ctyp_equal (cval_ctyp arg) CT_unit)) args
          in
          I_aux (I_funcall (destination, extern, callee, args), annot)
      | instr -> instr
    in
    let body = List.map (map_instr_cval unique_unit) body |> List.map (map_instr rewrite_call) in
    filter_instrs
      (function
        | I_aux
            ( ( I_decl (CT_unit, _)
              | I_init (CT_unit, _, _)
              | I_reinit (CT_unit, _, _)
              | I_reset (CT_unit, _)
              | I_clear (CT_unit, _) ),
              _
            ) ->
            false
        | I_aux (I_copy (destination, _), _) when ctyp_equal (clexp_ctyp destination) CT_unit -> false
        | _ -> true
        )
      body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, erase_body body), def_annot)
  | CDEF_startup (id, body) -> CDEF_aux (CDEF_startup (id, erase_body body), def_annot)
  | CDEF_finish (id, body) -> CDEF_aux (CDEF_finish (id, erase_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* A goto whose target label is the immediately following instruction has no
   effect.  JIB cleanup lowering creates this shape inside many early-return
   branches before jumping on to the shared function exit.  Delete only that
   adjacent edge; the label remains available to any non-local predecessor and
   the ordinary unused-label cleanup can remove it when this was its sole use. *)
let remove_fallthrough_gotos (CDEF_aux (aux, def_annot)) =
  let rewrite_lists instrs =
    let rec rewrite = function
      | I_aux (I_goto target, _) :: (I_aux (I_label label, _) as labelled) :: rest when String.equal target label ->
          labelled :: rewrite rest
      | instr :: rest -> instr :: rewrite rest
      | [] -> []
    in
    rewrite instrs
  in
  let rewrite_body body = List.map (map_instrs rewrite_lists) body |> rewrite_lists in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* For a unit-valued function, a goto to the label immediately preceding its
   final unit return is exactly an early C [return;].  Reconstruct that
   structured exit after cleanup/lifetime lowering has finished.  This is
   deliberately limited to the terminal label and unit result: exception and
   intermediate cleanup labels keep their original control flow. *)
let return_from_terminal_unit_label ctx (CDEF_aux (aux, def_annot)) =
  let returns_unit id =
    match Bindings.find_opt id ctx.valspecs with
    | Some (_, _, ret_ctyp, _) -> ctyp_equal ret_ctyp CT_unit
    | None -> false
  in
  let rewrite_body id body =
    if not (returns_unit id) then body
    else (
      match List.rev body with
      | (I_aux (I_return value, _) as terminal_return)
        :: (I_aux (I_label terminal_label, _) as terminal_label_instr)
        :: reversed
        when ctyp_equal (cval_ctyp value) CT_unit ->
          let rewrite_goto = function
            | I_aux (I_goto target, annot) when String.equal target terminal_label ->
                I_aux (I_return (V_lit (VL_unit, CT_unit)), annot)
            | instr -> instr
          in
          List.rev (terminal_return :: terminal_label_instr :: List.map (map_instr rewrite_goto) reversed)
      | _ -> body
    )
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body id body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Representation specialization can turn a return-via-pointer function into
   an ordinary scalar-returning C function after cleanup lowering has already
   introduced a shared [end_function] label.  When an early arm does nothing
   except assign that scalar result and jump to the terminal return, emit the
   return in the arm itself.  This is the stack-result analogue of
   [return_from_terminal_unit_label]; restricting the rewrite to an assignment
   or call followed only by untargeted cleanup labels and the jump preserves
   any real cleanup between production of the result and the function exit. *)
let return_from_terminal_stack_label (CDEF_aux (aux, def_annot)) =
  let same_name left right = Name.compare left right = 0 in
  let rewrite_body body =
    match List.rev body with
    | (I_aux (I_return (V_id (result, result_ctyp)), _) as terminal_return)
      :: (I_aux (I_label terminal_label, _) as terminal_label_instr)
      :: reversed ->
        let targeted_labels = ref Util.StringSet.empty in
        List.iter
          (fun instr ->
            ignore
              (map_instr
                 (fun (I_aux (aux, _) as sub) ->
                   ( match aux with
                   | I_goto target | I_jump (_, target) -> targeted_labels := Util.StringSet.add target !targeted_labels
                   | _ -> ()
                   );
                   sub
                 )
                 instr
              )
          )
          body;
        let rec after_terminal_jump = function
          | I_aux (I_goto target, _) :: rest when String.equal target terminal_label -> Some rest
          | I_aux (I_label label, _) :: rest when not (Util.StringSet.mem label !targeted_labels) ->
              after_terminal_jump rest
          | _ -> None
        in
        let rewrite_lists instrs =
          let rec rewrite = function
            | (I_aux (I_copy (CL_id (destination, destination_ctyp), value), copy_aux) as copy) :: tail
              when same_name destination result && ctyp_equal destination_ctyp result_ctyp
                   && ctyp_equal (cval_ctyp value) result_ctyp -> (
                match after_terminal_jump tail with
                | Some rest -> I_aux (I_return value, copy_aux) :: rewrite rest
                | None -> copy :: rewrite tail
              )
            | ( I_aux (I_funcall (CR_one (CL_id (destination, destination_ctyp)), extern, callee, args), call_aux) as
                call
              )
              :: tail
              when same_name destination result && ctyp_equal destination_ctyp result_ctyp -> (
                match after_terminal_jump tail with
                | Some rest ->
                    I_aux (I_funcall (CR_one (CL_id (Return (-1), result_ctyp)), extern, callee, args), call_aux)
                    :: rewrite rest
                | None -> call :: rewrite tail
              )
            | instr :: rest -> instr :: rewrite rest
            | [] -> []
          in
          rewrite instrs
        in
        List.rev (terminal_return :: terminal_label_instr :: List.map (map_instrs rewrite_lists) reversed)
        |> rewrite_lists
    | _ -> body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Fold pure single-use copies into their consumer. A local declared and
   immediately assigned a cval (`x = v.sender;`) is substituted into the
   instructions that read it, removing the declaration and the copy, when it
   is provably safe:

   - every root name the cval reads is a body-declared local or an argument,
     and none of them is written again in the remainder of the block, so the
     substituted expression still denotes the copied value;
   - no label sits between the copy and the final read, so no jump can land
     inside the propagation window with different root values;
   - the local is read exactly once (arbitrary cval), or the cval is a bare
     variable or literal (any read count), so no work is duplicated;
   - the local is never written again.

   cvals are pure by construction, so dropping an unread copy is sound. *)
let optimize_pure_copies = ref false

(* JIB's cleanup lowering deliberately leaves a common structured-C shape:

     label end_function;
     return result;

   even when no control-flow edge targets the label.  ANF fragments also put
   a single assignment in a lexical block after their inner temporaries have
   disappeared.  Neither artifact carries meaning at this point, but both
   prevent the local copy propagation below from seeing adjacent producers
   and consumers.  Remove only provably untargeted labels and declaration-free
   singleton copy blocks; labels that participate in exception/cleanup flow
   and blocks that still own locals remain untouched. *)
let simplify_pure_copy_scaffolding (CDEF_aux (aux, def_annot)) =
  let rewrite_body body =
    let targeted_labels = ref Util.StringSet.empty in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               ( match aux with
               | I_goto target | I_jump (_, target) -> targeted_labels := Util.StringSet.add target !targeted_labels
               | _ -> ()
               );
               sub
             )
             instr
          )
      )
      body;
    let rewrite_lists instrs =
      List.concat_map
        (function
          | I_aux (I_label label, _) when not (Util.StringSet.mem label !targeted_labels) -> []
          | I_aux (I_block [], _) -> []
          | I_aux (I_block body, _)
            when not (List.exists (function I_aux ((I_decl _ | I_init _ | I_reset _), _) -> true | _ -> false) body) ->
              body
          | instr -> [instr]
          )
        instrs
    in
    let rec fixpoint n body =
      let rewritten = List.map (map_instrs rewrite_lists) body |> rewrite_lists in
      if n = 0 || rewritten = body then rewritten else fixpoint (n - 1) rewritten
    in
    let body = fixpoint 2 body in
    let referenced = ref NameSet.empty in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               ( match aux with
               | I_decl _ -> ()
               | _ -> referenced := NameSet.union !referenced (instr_ids ~direct:true sub)
               );
               sub
             )
             instr
          )
      )
      body;
    filter_instrs (function I_aux (I_decl (_, name), _) -> NameSet.mem name !referenced | _ -> true) body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | CDEF_let (number, bindings, body) -> CDEF_aux (CDEF_let (number, bindings, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* JIB uses lexical blocks to delimit ANF temporaries even when all of those
   temporaries have fixed stack representations. In optimized C a block may be
   removed when every declaration it contains has a function-unique name:
   extending such a C local's lifetime cannot alias another local, and stack
   values have no create/kill lifetime protocol to preserve. Flattening here
   exposes producer/copy/consumer sequences to the ordinary copy passes below. *)
let flatten_unique_stack_blocks ctx (CDEF_aux (aux, def_annot)) =
  let rewrite_body body =
    let declaration_counts = ref NameMap.empty in
    let count_declaration name =
      let count = Option.value ~default:0 (NameMap.find_opt name !declaration_counts) in
      declaration_counts := NameMap.add name (count + 1) !declaration_counts
    in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               ( match aux with
               | I_decl (_, name) | I_init (_, name, _) | I_reinit (_, name, _) | I_reset (_, name) ->
                   count_declaration name
               | _ -> ()
               );
               sub
             )
             instr
          )
      )
      body;
    let block_is_flattenable block =
      let safe = ref true in
      List.iter
        (fun instr ->
          ignore
            (map_instr
               (fun (I_aux (aux, _) as sub) ->
                 ( match aux with
                 | I_decl (ctyp, name) | I_init (ctyp, name, _) | I_reinit (ctyp, name, _) | I_reset (ctyp, name) ->
                     if
                       (not (is_stack_ctyp ctx ctyp))
                       || Option.value ~default:0 (NameMap.find_opt name !declaration_counts) <> 1
                     then safe := false
                 | I_clear (ctyp, _) when not (is_stack_ctyp ctx ctyp) -> safe := false
                 | _ -> ()
                 );
                 sub
               )
               instr
            )
        )
        block;
      !safe
    in
    let rewrite_lists instrs =
      List.concat_map
        (function I_aux (I_block block, _) when block_is_flattenable block -> block | instr -> [instr])
        instrs
    in
    let rec fixpoint n body =
      let rewritten = List.map (map_instrs rewrite_lists) body |> rewrite_lists in
      if n = 0 || rewritten = body then rewritten else fixpoint (n - 1) rewritten
    in
    fixpoint 4 body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Recover the short-circuit boolean expression represented by JIB's ANF
   diamond. The right operand remains under C's &&/|| short-circuit operator,
   so this changes neither its evaluation condition nor its order. Cvals are
   pure; effectful calls remain explicit instructions and cannot match here. *)
let collapse_short_circuit_booleans (CDEF_aux (aux, def_annot)) =
  let bool_literal expected = function V_lit (VL_bool actual, CT_bool) -> Bool.equal expected actual | _ -> false in
  let assigned_value destination = function
    | instrs -> (
        let rec meaningful = function
          | I_aux (I_clear (ctyp, _), _) :: rest when ctyp_equal ctyp CT_bool -> meaningful rest
          | I_aux (I_block block, _) :: rest -> meaningful block @ meaningful rest
          | instr :: rest -> instr :: meaningful rest
          | [] -> []
        in
        match meaningful instrs with
        | [I_aux (I_copy (CL_id (assigned, assigned_ctyp), value), _)]
          when Name.compare destination assigned = 0 && ctyp_equal assigned_ctyp CT_bool ->
            Some value
        | _ -> None
      )
  in
  let expression condition then_value else_value =
    if bool_literal false else_value then Some (V_call (Band, [condition; then_value]))
    else if bool_literal true then_value then Some (V_call (Bor, [condition; else_value]))
    else if bool_literal false then_value then Some (V_call (Band, [V_call (Bnot, [condition]); else_value]))
    else if bool_literal true else_value then Some (V_call (Bor, [V_call (Bnot, [condition]); then_value]))
    else None
  in
  let rewrite_lists instrs =
    let rec rewrite = function
      | (I_aux (I_decl (result_ctyp, result), _) as result_declaration)
        :: (I_aux (I_decl (temporary_ctyp, temporary), _) as temporary_declaration)
        :: I_aux (I_if (condition, then_instrs, else_instrs), if_aux)
        :: I_aux (I_copy (CL_id (assigned_result, assigned_result_ctyp), V_id (source, source_ctyp)), copy_aux)
        :: rest
        when ctyp_equal result_ctyp CT_bool && ctyp_equal temporary_ctyp CT_bool
             && Name.compare result assigned_result = 0
             && Name.compare temporary source = 0
             && ctyp_equal result_ctyp assigned_result_ctyp
             && ctyp_equal temporary_ctyp source_ctyp -> (
          match (assigned_value temporary then_instrs, assigned_value temporary else_instrs) with
          | Some then_value, Some else_value -> (
              match expression condition then_value else_value with
              | Some value ->
                  result_declaration :: I_aux (I_copy (CL_id (result, CT_bool), value), copy_aux) :: rewrite rest
              | None ->
                  result_declaration :: temporary_declaration
                  :: I_aux (I_if (condition, then_instrs, else_instrs), if_aux)
                  :: I_aux (I_copy (CL_id (assigned_result, assigned_result_ctyp), V_id (source, source_ctyp)), copy_aux)
                  :: rewrite rest
            )
          | _ ->
              result_declaration :: temporary_declaration
              :: I_aux (I_if (condition, then_instrs, else_instrs), if_aux)
              :: I_aux (I_copy (CL_id (assigned_result, assigned_result_ctyp), V_id (source, source_ctyp)), copy_aux)
              :: rewrite rest
        )
      | (I_aux (I_decl (declared_ctyp, destination), _) as declaration)
        :: I_aux (I_if (condition, then_instrs, else_instrs), if_aux)
        :: rest
        when ctyp_equal declared_ctyp CT_bool -> (
          match (assigned_value destination then_instrs, assigned_value destination else_instrs) with
          | Some then_value, Some else_value -> (
              match expression condition then_value else_value with
              | Some value ->
                  declaration :: I_aux (I_copy (CL_id (destination, CT_bool), value), if_aux) :: rewrite rest
              | None -> declaration :: I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rewrite rest
            )
          | _ -> declaration :: I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rewrite rest
        )
      | instr :: rest -> instr :: rewrite rest
      | [] -> []
    in
    rewrite instrs
  in
  let rewrite_body body = List.map (map_instrs rewrite_lists) body |> rewrite_lists in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Merge repeated bodies in adjacent conditional arms while retaining C's
   short-circuit evaluation order.  JIB commonly preserves a Sail conditional
   ladder as

     if (first) { same } else if (second) { same } else { other }

   even though both conditions are already pure cvals.  Combining the tests
   removes the duplicated body and gives the later copy/return passes one
   branch rather than two equivalent producers.  The symmetric form, where
   the first and final bodies are equal, becomes [!first && second].  Compare
   instructions without their source annotations: separately lowered copies
   of the same arm naturally carry different locations but have identical JIB
   semantics. *)
let merge_repeated_conditional_branches (CDEF_aux (aux, def_annot)) =
  let call_kind_equal left right =
    match (left, right) with
    | Call _, Call _ -> true
    | Extern left_ctyp, Extern right_ctyp -> ctyp_equal left_ctyp right_ctyp
    | _ -> false
  in
  let uid_equal (left_id, left_ctyps) (right_id, right_ctyps) =
    Id.compare left_id right_id = 0
    && List.compare_lengths left_ctyps right_ctyps = 0
    && List.for_all2 ctyp_equal left_ctyps right_ctyps
  in
  let call_return_equal left right =
    match (left, right) with
    | CR_one (CL_id (Return _, left_ctyp)), CR_one (CL_id (Return _, right_ctyp)) -> ctyp_equal left_ctyp right_ctyp
    | _ -> left = right
  in
  let name_equal left right =
    match (left, right) with
    | Gen (lv1, lv2, ln, _, _), Gen (rv1, rv2, rn, _, _) -> lv1 = rv1 && lv2 = rv2 && ln = rn
    | Name (left_id, left_ssa), Name (right_id, right_ssa) -> Id.compare left_id right_id = 0 && left_ssa = right_ssa
    | _ -> left = right
  in
  let cval_equal left right =
    match (left, right) with
    | V_id (left_name, left_ctyp), V_id (right_name, right_ctyp) ->
        name_equal left_name right_name && ctyp_equal left_ctyp right_ctyp
    | _ -> left = right
  in
  let rec instrs_equal left right = List.length left = List.length right && List.for_all2 instr_equal left right
  and instr_equal (I_aux (left, _)) (I_aux (right, _)) =
    match (left, right) with
    | ( I_funcall (left_return, left_kind, left_uid, left_args),
        I_funcall (right_return, right_kind, right_uid, right_args) ) ->
        let return_equal = call_return_equal left_return right_return in
        let kind_equal = call_kind_equal left_kind right_kind in
        let function_equal = uid_equal left_uid right_uid in
        let args_equal =
          List.compare_lengths left_args right_args = 0 && List.for_all2 cval_equal left_args right_args
        in
        return_equal && kind_equal && function_equal && args_equal
    | I_if (left_condition, left_then, left_else), I_if (right_condition, right_then, right_else) ->
        left_condition = right_condition && instrs_equal left_then right_then && instrs_equal left_else right_else
    | I_block left, I_block right | I_try_block left, I_try_block right -> instrs_equal left right
    | _ -> left = right
  in
  let rec exits = function
    | [] -> false
    | branch -> (
        match List.rev branch with
        | I_aux (I_exit _, _) :: _
        | I_aux (I_return _, _) :: _
        | I_aux (I_copy (CL_id (Return _, _), _), _) :: _
        | I_aux (I_funcall (CR_one (CL_id (Return _, _)), _, _, _), _) :: _ ->
            true
        | I_aux (I_if (_, then_instrs, else_instrs), _) :: _ -> exits then_instrs && exits else_instrs
        | I_aux (I_block instrs, _) :: _ -> exits instrs
        | _ -> false
      )
  in
  let rewrite_lists instrs =
    let rec rewrite = function
      | I_aux (I_if (first, first_body, []), if_aux) :: I_aux (I_if (second, second_body, []), _) :: rest
        when exits first_body && instrs_equal first_body second_body ->
          I_aux (I_if (V_call (Bor, [first; second]), first_body, []), if_aux) :: rewrite rest
      | I_aux (I_if (first, first_body, [I_aux (I_if (second, second_body, other_body), _)]), if_aux) :: rest
        when instrs_equal first_body second_body ->
          I_aux (I_if (V_call (Bor, [first; second]), first_body, other_body), if_aux) :: rewrite rest
      | I_aux (I_if (first, first_body, [I_aux (I_if (second, second_body, final_body), _)]), if_aux) :: rest
        when instrs_equal first_body final_body ->
          I_aux (I_if (V_call (Band, [V_call (Bnot, [first]); second]), second_body, first_body), if_aux)
          :: rewrite rest
      | I_aux (I_if (first, [I_aux (I_if (second, nested_body, middle_body), _)], final_body), if_aux) :: rest
        when instrs_equal middle_body final_body ->
          I_aux (I_if (V_call (Band, [first; second]), nested_body, final_body), if_aux) :: rewrite rest
      | instr :: rest -> instr :: rewrite rest
      | [] -> []
    in
    rewrite instrs
  in
  let rewrite_body body =
    let rec fixpoint n body =
      let rewritten = List.map (map_instrs rewrite_lists) body |> rewrite_lists in
      if n = 0 || rewritten = body then rewritten else fixpoint (n - 1) rewritten
    in
    fixpoint 4 body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Representation specialization can prove a predicate after JIB has already
   formed its control-flow graph. Remove those literal-condition branches at
   the IR level so the ordinary copy, scope, and declaration cleanups see only
   the path that can execute. *)
let prune_constant_branches (CDEF_aux (aux, def_annot)) =
  let rewrite_lists instrs =
    List.concat_map
      (function
        | I_aux (I_if (V_lit (VL_bool condition, CT_bool), then_instrs, else_instrs), _) ->
            if condition then then_instrs else else_instrs
        | instr -> [instr]
        )
      instrs
  in
  let rewrite_body body =
    let rec fixpoint n body =
      let rewritten = List.map (map_instrs rewrite_lists) body |> rewrite_lists in
      if n = 0 || rewritten = body then rewritten else fixpoint (n - 1) rewritten
    in
    fixpoint 4 body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Reassemble the field-by-field JIB lowering of a complete stack aggregate
   into one pure value.  This is deliberately limited to complete records and
   tuples whose field assignments require no conversion.  The resulting
   [V_struct] or [V_tuple] can then participate in ordinary copy propagation,
   which removes both aggregate-construction temporaries and their scopes. *)
let fold_stack_aggregate_construction ctx (CDEF_aux (aux, def_annot)) =
  let preserve_assignment_conversion target_ctyp value =
    let source_ctyp = cval_ctyp value in
    if ctyp_equal source_ctyp target_ctyp then Some value
    else (
      match (target_ctyp, source_ctyp) with
      | CT_fuint width, (CT_fuint _ | CT_fint _ | CT_fbits _ | CT_constant _) -> Some (V_call (Unsigned width, [value]))
      | CT_fint width, (CT_fuint _ | CT_fint _ | CT_fbits _ | CT_constant _) -> Some (V_call (Signed width, [value]))
      | _ -> None
    )
  in
  let expected_fields = function
    | CT_struct (id, _) -> (
        match Bindings.find_opt id ctx.records with
        | Some (_, fields) -> Some (List.map fst (Bindings.bindings fields))
        | None -> None
      )
    | _ -> None
  in
  let complete expected actual =
    let actual_count = List.length actual in
    let expected = IdSet.of_list expected in
    let actual = List.fold_left (fun fields (field, _) -> IdSet.add field fields) IdSet.empty actual in
    IdSet.cardinal expected = actual_count && IdSet.equal expected actual
  in
  let rec reads destination = function
    | V_id (name, _) -> Name.compare destination name = 0
    | V_member _ | V_lit _ -> false
    | V_call (_, values) | V_tuple values -> List.exists (reads destination) values
    | V_field (value, _, _) | V_tuple_member (value, _, _) | V_ctor_kind (value, _) | V_ctor_unwrap (value, _, _) ->
        reads destination value
    | V_struct (fields, _) -> List.exists (fun (_, value) -> reads destination value) fields
  in
  let collect destination destination_ctyp instrs =
    let rec collect rev_fields = function
      | I_aux (I_copy (CL_field (CL_id (base, base_ctyp), field, field_ctyp), value), _) :: rest
        when Name.compare destination base = 0
             && ctyp_equal destination_ctyp base_ctyp
             && ctyp_equal field_ctyp (cval_ctyp value)
             && not (reads destination value) ->
          collect ((field, value) :: rev_fields) rest
      | rest -> (List.rev rev_fields, rest)
    in
    collect [] instrs
  in
  let collect_tuple destination destination_ctyp length instrs =
    let rec collect rev_fields = function
      | I_aux (I_copy (CL_tuple (CL_id (base, base_ctyp), index), value), _) :: rest
        when Name.compare destination base = 0
             && ctyp_equal destination_ctyp base_ctyp && index >= 0 && index < length
             && ( match destination_ctyp with
               | CT_tup field_ctyps -> ctyp_equal (List.nth field_ctyps index) (cval_ctyp value)
               | _ -> false
               )
             && not (reads destination value) ->
          collect ((index, value) :: rev_fields) rest
      | rest -> (List.rev rev_fields, rest)
    in
    collect [] instrs
  in
  let complete_tuple length fields =
    List.length fields = length
    && List.sort_uniq Int.compare (List.map fst fields) = Util.list_init length (fun index -> index)
  in
  let collect_converted_tuple destination destination_ctyp field_ctyps instrs =
    let length = List.length field_ctyps in
    let rec collect rev_fields = function
      | I_aux (I_copy (CL_tuple (CL_id (base, base_ctyp), index), value), _) :: rest
        when Name.compare destination base = 0
             && ctyp_equal destination_ctyp base_ctyp && index >= 0 && index < length
             && not (List.mem_assoc index rev_fields) -> (
          match preserve_assignment_conversion (List.nth field_ctyps index) value with
          | Some value -> collect ((index, value) :: rev_fields) rest
          | None -> (List.rev rev_fields, rest)
        )
      | rest -> (List.rev rev_fields, rest)
    in
    collect [] instrs
  in
  let rewrite_lists instrs =
    let rec rewrite = function
      | I_aux
          (I_copy (CL_id (destination, (CT_tup target_ctyps as destination_ctyp)), (V_tuple values as source)), copy_aux)
        :: rest
        when List.length target_ctyps = List.length values ->
          let converted = List.map2 preserve_assignment_conversion target_ctyps values in
          if List.for_all Option.is_some converted && not (ctyp_equal destination_ctyp (cval_ctyp source)) then (
            let converted = List.map Option.get converted in
            I_aux (I_copy (CL_id (destination, destination_ctyp), V_tuple converted), copy_aux) :: rewrite rest
          )
          else I_aux (I_copy (CL_id (destination, destination_ctyp), source), copy_aux) :: rewrite rest
      | (I_aux (I_decl (ctyp, destination), declaration_aux) as declaration) :: rest when is_stack_ctyp ctx ctyp -> (
          match expected_fields ctyp with
          | Some expected ->
              let fields, remaining = collect destination ctyp rest in
              if fields <> [] && complete expected fields then
                declaration
                :: I_aux (I_copy (CL_id (destination, ctyp), V_struct (fields, ctyp)), declaration_aux)
                :: rewrite remaining
              else declaration :: rewrite rest
          | None -> (
              match ctyp with
              | CT_tup field_ctyps ->
                  let fields, remaining = collect_tuple destination ctyp (List.length field_ctyps) rest in
                  if fields <> [] && complete_tuple (List.length field_ctyps) fields then (
                    let values =
                      List.sort (fun (left, _) (right, _) -> Int.compare left right) fields |> List.map snd
                    in
                    declaration
                    :: I_aux (I_copy (CL_id (destination, ctyp), V_tuple values), declaration_aux)
                    :: rewrite remaining
                  )
                  else declaration :: rewrite rest
              | _ -> declaration :: rewrite rest
            )
        )
      | (I_aux (I_copy (CL_tuple (CL_id (destination, destination_ctyp), _), _), copy_aux) as first) :: rest -> (
          match destination_ctyp with
          | CT_tup field_ctyps ->
              let fields, remaining =
                collect_converted_tuple destination destination_ctyp field_ctyps (first :: rest)
              in
              if complete_tuple (List.length field_ctyps) fields then (
                let values = List.sort (fun (left, _) (right, _) -> Int.compare left right) fields |> List.map snd in
                I_aux (I_copy (CL_id (destination, destination_ctyp), V_tuple values), copy_aux) :: rewrite remaining
              )
              else first :: rewrite rest
          | _ -> first :: rewrite rest
        )
      | instr :: rest -> instr :: rewrite rest
      | [] -> []
    in
    rewrite instrs
  in
  let rewrite_body body = List.map (map_instrs rewrite_lists) body |> rewrite_lists in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Turn a structured expression whose one arm exits into an early guard.
   Sail often needs an arm to retain dependent-type facts, but C no longer
   needs that lexical proof scope after JIB has fixed every ctyp:

     if (valid) { normal } else { fatal_error(...); exit; }

   becomes

     if (!valid) { fatal_error(...); exit; }
     normal

   Returns use the same rewrite, eliminating [else] after a value or unit
   return.  Only function-unique stack declarations leave their branch scope;
   otherwise the continuing arm is retained as an explicit block. This is the
   same lifetime/name proof used by [flatten_unique_stack_blocks]. *)
let flatten_terminal_guards ctx (CDEF_aux (aux, def_annot)) =
  let rewrite_body body =
    let declaration_counts = ref NameMap.empty in
    let count_declaration name =
      let count = Option.value ~default:0 (NameMap.find_opt name !declaration_counts) in
      declaration_counts := NameMap.add name (count + 1) !declaration_counts
    in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               ( match aux with
               | I_decl (_, name) | I_init (_, name, _) | I_reinit (_, name, _) | I_reset (_, name) ->
                   count_declaration name
               | _ -> ()
               );
               sub
             )
             instr
          )
      )
      body;
    let movable branch =
      let safe = ref true in
      List.iter
        (fun instr ->
          ignore
            (map_instr
               (fun (I_aux (aux, _) as sub) ->
                 ( match aux with
                 | I_decl (ctyp, name) | I_init (ctyp, name, _) | I_reinit (ctyp, name, _) | I_reset (ctyp, name) ->
                     if
                       (not (is_stack_ctyp ctx ctyp))
                       || Option.value ~default:0 (NameMap.find_opt name !declaration_counts) <> 1
                     then safe := false
                 | I_clear (ctyp, _) when not (is_stack_ctyp ctx ctyp) -> safe := false
                 | _ -> ()
                 );
                 sub
               )
               instr
            )
        )
        branch;
      !safe
    in
    let rec exits = function
      | [] -> false
      | branch -> (
          match List.rev branch with
          | I_aux (I_exit _, _) :: _ -> true
          | I_aux (I_funcall (CR_one (CL_id (Return _, _)), _, _, _), _) :: _ -> true
          | I_aux (I_return _, _) :: _ -> true
          | I_aux (I_if (_, then_instrs, else_instrs), _) :: _ -> exits then_instrs && exits else_instrs
          | I_aux (I_block instrs, _) :: _ -> exits instrs
          | _ -> false
        )
    in
    let contains_label branch =
      List.exists
        (fun instr ->
          let found = ref false in
          ignore
            (map_instr
               (fun (I_aux (aux, _) as sub) ->
                 (match aux with I_label _ -> found := true | _ -> ());
                 sub
               )
               instr
            );
          !found
        )
        branch
    in
    let continue_with branch branch_aux continuation =
      let branch = if movable branch then branch else [I_aux (I_block branch, branch_aux)] in
      branch @ continuation
    in
    let rec rewrite = function
      (* A flattened match can leave its successful, terminal continuation in
         the only populated branch and the fatal/default arm as the following
         statements.  Turn that fallthrough terminal path into an early guard,
         lifting the successful branch (and any private join label it owns)
         back into the surrounding sequence. *)
      | I_aux (I_if (condition, then_instrs, []), if_aux) :: rest
        when contains_label then_instrs && exits then_instrs && exits rest ->
          let then_instrs = rewrite then_instrs in
          let rest = rewrite rest in
          I_aux (I_if (V_call (Bnot, [condition]), rest, []), if_aux) :: continue_with then_instrs if_aux []
      | I_aux (I_if (condition, [], else_instrs), if_aux) :: rest
        when contains_label else_instrs && exits else_instrs && exits rest ->
          let else_instrs = rewrite else_instrs in
          let rest = rewrite rest in
          I_aux (I_if (condition, rest, []), if_aux) :: continue_with else_instrs if_aux []
      | I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rest ->
          let then_instrs = rewrite then_instrs in
          let else_instrs = rewrite else_instrs in
          let then_exits = exits then_instrs in
          let else_exits = exits else_instrs in
          if then_exits && else_exits then
            I_aux (I_if (condition, then_instrs, []), if_aux) :: continue_with else_instrs if_aux (rewrite rest)
          else if else_exits then
            I_aux (I_if (V_call (Bnot, [condition]), else_instrs, []), if_aux)
            :: continue_with then_instrs if_aux (rewrite rest)
          else if then_exits then
            I_aux (I_if (condition, then_instrs, []), if_aux) :: continue_with else_instrs if_aux (rewrite rest)
          else I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rewrite rest
      | I_aux (I_block block, block_aux) :: rest -> I_aux (I_block (rewrite block), block_aux) :: rewrite rest
      | I_aux (I_try_block block, block_aux) :: rest -> I_aux (I_try_block (rewrite block), block_aux) :: rewrite rest
      | instr :: rest -> instr :: rewrite rest
      | [] -> []
    in
    rewrite body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Preserve assignment conversion semantics while eliminating adjacent copy
   chains.  In both patterns the intermediate and consumer have the same JIB
   type, so assigning the producer directly performs the same C conversion as
   assigning it through the temporary first.  This intentionally does not
   substitute a differently typed producer into arbitrary arithmetic. *)
let fold_copy_conversions (CDEF_aux (aux, def_annot)) =
  let rewrite_lists instrs =
    let rec rewrite = function
      | I_aux (I_funcall (CR_one (CL_id (temporary, temporary_ctyp)), extern, callee, args), call_aux)
        :: I_aux (I_return (V_id (result, result_ctyp)), _)
        :: rest
        when Name.compare temporary result = 0 && ctyp_equal temporary_ctyp result_ctyp ->
          I_aux (I_funcall (CR_one (CL_id (Return (-1), result_ctyp)), extern, callee, args), call_aux) :: rewrite rest
      | I_aux (I_init (temporary_ctyp, temporary, Init_cval cval), _)
        :: I_aux (I_return (V_id (result, result_ctyp)), return_aux)
        :: rest
        when Name.compare temporary result = 0
             && ctyp_equal temporary_ctyp result_ctyp
             && ctyp_equal temporary_ctyp (cval_ctyp cval) ->
          I_aux (I_return cval, return_aux) :: rewrite rest
      | I_aux (I_copy (CL_id (temporary, temporary_ctyp), cval), _)
        :: I_aux (I_return (V_id (result, result_ctyp)), return_aux)
        :: rest
        when Name.compare temporary result = 0
             && ctyp_equal temporary_ctyp result_ctyp
             && ctyp_equal temporary_ctyp (cval_ctyp cval) ->
          I_aux (I_return cval, return_aux) :: rewrite rest
      | I_aux (I_copy (CL_id (temporary, temporary_ctyp), cval), _)
        :: I_aux (I_copy (destination, V_id (source, source_ctyp)), copy_aux)
        :: rest
        when Name.compare temporary source = 0
             && ctyp_equal temporary_ctyp source_ctyp
             && ctyp_equal temporary_ctyp (clexp_ctyp destination)
             && not (List.exists (fun instr -> instr_references ~read:temporary ~direct:false instr) rest) ->
          I_aux (I_copy (destination, cval), copy_aux) :: rewrite rest
      | I_aux (I_funcall (CR_one (CL_id (temporary, temporary_ctyp)), extern, callee, args), call_aux)
        :: I_aux (I_copy (destination, V_id (source, source_ctyp)), _)
        :: rest
        when Name.compare temporary source = 0
             && ctyp_equal temporary_ctyp source_ctyp
             && ctyp_equal temporary_ctyp (clexp_ctyp destination)
             && not (List.exists (fun instr -> instr_references ~read:temporary ~direct:false instr) rest) ->
          I_aux (I_funcall (CR_one destination, extern, callee, args), call_aux) :: rewrite rest
      | instr :: rest -> instr :: rewrite rest
      | [] -> []
    in
    rewrite instrs
  in
  let rewrite_body body =
    let rec fixpoint n body =
      let rewritten = List.map (map_instrs rewrite_lists) body |> rewrite_lists in
      if n = 0 || rewritten = body then rewritten else fixpoint (n - 1) rewritten
    in
    fixpoint 2 body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* A stack result selected by structured control flow does not need a mutable
   join temporary when every branch produces the result exactly once:

     if (condition) result = f(); else result = zero;
     return result;

   Sink the return into both branches.  A terminal function call is marked by
   restoring JIB's Return destination; code generation emits that form as a C
   return expression.  Calls followed by exception handling are deliberately
   not terminal, so the check remains between the call and the eventual
   return. *)
let sink_terminal_stack_returns (CDEF_aux (aux, def_annot)) =
  let same_name left right = Name.compare left right = 0 in
  let preserve_assignment_conversion target_ctyp value =
    let source_ctyp = cval_ctyp value in
    if ctyp_equal source_ctyp target_ctyp then Some value
    else (
      match (target_ctyp, source_ctyp) with
      | CT_fuint width, (CT_fuint _ | CT_fint _ | CT_fbits _ | CT_constant _) -> Some (V_call (Unsigned width, [value]))
      | CT_fint width, (CT_fuint _ | CT_fint _ | CT_fbits _ | CT_constant _) -> Some (V_call (Signed width, [value]))
      | _ -> None
    )
  in
  let sink_tuple result result_ctyp return_aux instrs =
    match result_ctyp with
    | CT_tup field_ctyps ->
        let length = List.length field_ctyps in
        let rec collect fields = function
          | I_aux (I_copy (CL_tuple (CL_id (destination, destination_ctyp), index), value), _) :: reversed
            when same_name destination result && ctyp_equal destination_ctyp result_ctyp && index >= 0 && index < length
                 && not (List.mem_assoc index fields) -> (
              match preserve_assignment_conversion (List.nth field_ctyps index) value with
              | Some value -> collect ((index, value) :: fields) reversed
              | None -> None
            )
          | reversed when List.length fields = length ->
              let values = List.sort (fun (left, _) (right, _) -> Int.compare left right) fields |> List.map snd in
              Some (List.rev (I_aux (I_return (V_tuple values), return_aux) :: reversed))
          | _ -> None
        in
        collect [] (List.rev instrs)
    | _ -> None
  in
  let rec sink result result_ctyp return_aux instrs =
    match sink_tuple result result_ctyp return_aux instrs with
    | Some instrs -> Some instrs
    | None -> (
        match List.rev instrs with
        | I_aux (I_copy (CL_id (destination, destination_ctyp), cval), _) :: rev_prefix
          when same_name destination result && ctyp_equal destination_ctyp result_ctyp
               && ctyp_equal (cval_ctyp cval) result_ctyp ->
            Some (List.rev (I_aux (I_return cval, return_aux) :: rev_prefix))
        | I_aux (I_funcall (CR_one (CL_id (destination, destination_ctyp)), extern, callee, args), call_aux)
          :: rev_prefix
          when same_name destination result && ctyp_equal destination_ctyp result_ctyp ->
            Some
              (List.rev
                 (I_aux (I_funcall (CR_one (CL_id (Return (-1), result_ctyp)), extern, callee, args), call_aux)
                 :: rev_prefix
                 )
              )
        | I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rev_prefix -> (
            match (sink result result_ctyp return_aux then_instrs, sink result result_ctyp return_aux else_instrs) with
            | Some then_instrs, Some else_instrs ->
                Some (List.rev (I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rev_prefix))
            | _ -> None
          )
        | I_aux (I_block block, block_aux) :: rev_prefix -> (
            match sink result result_ctyp return_aux block with
            | Some block when rev_prefix = [] -> Some block
            | Some block -> Some (List.rev (I_aux (I_block block, block_aux) :: rev_prefix))
            | None -> None
          )
        | _ -> None
      )
  in
  let target_counts body =
    let counts = Hashtbl.create 16 in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               ( match aux with
               | I_goto label | I_jump (_, label) ->
                   Hashtbl.replace counts label (1 + Option.value ~default:0 (Hashtbl.find_opt counts label))
               | _ -> ()
               );
               sub
             )
             instr
          )
      )
      body;
    fun label -> Option.value ~default:0 (Hashtbl.find_opt counts label)
  in
  let label_counts body =
    let counts = Hashtbl.create 16 in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               ( match aux with
               | I_label label ->
                   Hashtbl.replace counts label (1 + Option.value ~default:0 (Hashtbl.find_opt counts label))
               | _ -> ()
               );
               sub
             )
             instr
          )
      )
      body;
    fun label -> Option.value ~default:0 (Hashtbl.find_opt counts label)
  in
  let split_at_label target instrs =
    let rec split prefix = function
      | I_aux (I_label label, _) :: rest when String.equal label target -> Some (List.rev prefix, rest)
      | instr :: rest -> split (instr :: prefix) rest
      | [] -> None
    in
    split [] instrs
  in
  let drop_terminal_goto instrs =
    match List.rev instrs with I_aux (I_goto label, _) :: prefix -> Some (List.rev prefix, label) | _ -> None
  in
  let split_at_jump instrs =
    let rec split prefix = function
      | I_aux (I_jump (condition, alternate), jump_aux) :: rest ->
          Some (List.rev prefix, condition, alternate, jump_aux, rest)
      | I_aux ((I_label _ | I_goto _ | I_return _ | I_exit _), _) :: _ -> None
      | instr :: rest -> split (instr :: prefix) rest
      | [] -> None
    in
    split [] instrs
  in
  let rec terminal = function
    | [] -> false
    | instrs -> (
        match List.rev instrs with
        | I_aux (I_exit _, _) :: _
        | I_aux (I_return _, _) :: _
        | I_aux (I_copy (CL_id (Return _, _), _), _) :: _
        | I_aux (I_funcall (CR_one (CL_id (Return _, _)), _, _, _), _) :: _ ->
            true
        | I_aux (I_if (_, then_instrs, else_instrs), _) :: _ -> terminal then_instrs && terminal else_instrs
        | I_aux (I_block instrs, _) :: _ -> terminal instrs
        | _ -> false
      )
  in
  let split_at_terminal_branch instrs =
    let rec split prefix = function
      | I_aux (I_jump (condition, alternate), jump_aux) :: rest ->
          Some (List.rev prefix, condition, alternate, jump_aux, rest, true)
      | I_aux (I_if (condition, [], [I_aux (I_goto alternate, _)]), if_aux) :: rest ->
          Some (List.rev prefix, condition, alternate, if_aux, rest, false)
      | I_aux (I_if (condition, [I_aux (I_goto alternate, _)], []), if_aux) :: rest ->
          Some (List.rev prefix, condition, alternate, if_aux, rest, true)
      | I_aux ((I_label _ | I_goto _ | I_return _ | I_exit _), _) :: _ -> None
      | instr :: rest -> split (instr :: prefix) rest
      | [] -> None
    in
    split [] instrs
  in
  let fold_terminal_copy_return instrs =
    match List.rev instrs with
    | I_aux (I_return (V_id (returned, return_ctyp)), return_aux)
      :: I_aux (I_copy (CL_id (assigned, assigned_ctyp), value), _)
      :: reversed
      when Name.compare returned assigned = 0
           && ctyp_equal return_ctyp assigned_ctyp
           && ctyp_equal (cval_ctyp value) assigned_ctyp ->
        List.rev (I_aux (I_return value, return_aux) :: reversed)
    | _ -> instrs
  in
  let fold_branch_condition prefix condition =
    match (List.rev prefix, condition) with
    | ( I_aux (I_copy (CL_id (assigned, assigned_ctyp), value), _) :: I_aux (I_decl (decl_ctyp, declared), _) :: reversed,
        V_id (read, read_ctyp) )
      when Name.compare assigned declared = 0
           && Name.compare assigned read = 0
           && ctyp_equal assigned_ctyp decl_ctyp && ctyp_equal assigned_ctyp read_ctyp ->
        (List.rev reversed, value)
    | _ -> (prefix, condition)
  in
  let rec structure_terminal_ladder targets labels ladder =
    match split_at_terminal_branch ladder with
    | Some (condition_prefix, condition, alternate_label, branch_aux, ladder_tail, alternate_on_true) -> (
        match split_at_label alternate_label ladder_tail with
        | Some (primary, alternate) when targets alternate_label = 1 && labels alternate_label = 1 && terminal primary
          -> (
            match structure_terminal_ladder targets labels alternate with
            | Some alternate ->
                let condition_prefix, condition = fold_branch_condition condition_prefix condition in
                let then_instrs, else_instrs =
                  if alternate_on_true then (alternate, primary) else (primary, alternate)
                in
                Some (condition_prefix @ [I_aux (I_if (condition, then_instrs, else_instrs), branch_aux)])
            | None -> None
          )
        | _ -> None
      )
    | None when terminal ladder -> Some (fold_terminal_copy_return ladder)
    | None -> None
  in
  let rec rewrite targets labels = function
    | (I_aux (I_if (_, [], [I_aux (I_goto _, _)]), _) as first_branch) :: tail
    | (I_aux (I_if (_, [I_aux (I_goto _, _)], []), _) as first_branch) :: tail -> (
        match structure_terminal_ladder targets labels (first_branch :: tail) with
        | Some structured -> structured
        | None -> (
            match first_branch with
            | I_aux (I_if (condition, then_instrs, else_instrs), if_aux) ->
                I_aux (I_if (condition, rewrite targets labels then_instrs, rewrite targets labels else_instrs), if_aux)
                :: rewrite targets labels tail
            | _ -> assert false
          )
      )
    (* An exhaustive multi-arm match is flattened by JIB into a ladder of
       conditional jumps.  Every selected arm jumps to one result label and
       the final arm falls through to it:

         jump c1 case2; arm1; goto finish;
         case2: jump c2 case3; arm2; goto finish;
         case3: arm3;
         finish: return result;

       Rebuild that ladder as nested structured conditionals, then sink the
       terminal return into each value-producing arm.  The target/label counts
       prove that all removed labels are private to this exact ladder.  An arm
       which already exits (for example fatal_error(...); exit(())) is kept as
       terminal even though it does not assign the result. *)
    | (I_aux (I_jump (_, first_alternate), first_jump_aux) as first_jump) :: tail -> (
        match structure_terminal_ladder targets labels (first_jump :: tail) with
        | Some structured -> structured
        | None -> (
            match split_at_label first_alternate tail with
            | Some (first_arm_with_goto, after_first_alternate)
              when targets first_alternate = 1 && labels first_alternate = 1 -> (
                match drop_terminal_goto first_arm_with_goto with
                | Some (_, finish_label) when labels finish_label = 1 -> (
                    match split_at_label finish_label after_first_alternate with
                    | Some (remaining_ladder, I_aux (I_return (V_id (result, result_ctyp)), return_aux) :: rest) -> (
                        let ladder =
                          (first_jump :: first_arm_with_goto)
                          @ (I_aux (I_label first_alternate, first_jump_aux) :: remaining_ladder)
                        in
                        let rec structure ladder =
                          match split_at_jump ladder with
                          | Some (condition_prefix, condition, alternate_label, jump_aux, ladder_tail) -> (
                              match split_at_label alternate_label ladder_tail with
                              | Some (primary_with_goto, alternate)
                                when targets alternate_label = 1 && labels alternate_label = 1 -> (
                                  match drop_terminal_goto primary_with_goto with
                                  | Some (primary, primary_finish) when String.equal primary_finish finish_label -> (
                                      match (sink result result_ctyp return_aux primary, structure alternate) with
                                      | Some primary, Some (alternate, gotos) ->
                                          Some
                                            ( condition_prefix @ [I_aux (I_if (condition, alternate, primary), jump_aux)],
                                              gotos + 1
                                            )
                                      | _ -> None
                                    )
                                  | _ -> None
                                )
                              | _ -> None
                            )
                          | None -> (
                              match drop_terminal_goto ladder with
                              | Some (final_arm, final_finish) when String.equal final_finish finish_label -> (
                                  match sink result result_ctyp return_aux final_arm with
                                  | Some final_arm -> Some (final_arm, 1)
                                  | None when terminal final_arm -> Some (final_arm, 1)
                                  | None -> None
                                )
                              | _ -> (
                                  match sink result result_ctyp return_aux ladder with
                                  | Some final_arm -> Some (final_arm, 0)
                                  | None when terminal ladder -> Some (ladder, 0)
                                  | None -> None
                                )
                            )
                        in
                        match structure ladder with
                        | Some (structured, gotos) when targets finish_label = gotos ->
                            structured @ rewrite targets labels rest
                        | _ -> first_jump :: rewrite targets labels tail
                      )
                    | _ -> first_jump :: rewrite targets labels tail
                  )
                | _ -> first_jump :: rewrite targets labels tail
              )
            | _ -> first_jump :: rewrite targets labels tail
          )
      )
    | I_aux (I_if (condition, then_instrs, else_instrs), if_aux)
      :: I_aux (I_return (V_id (result, result_ctyp)), return_aux)
      :: rest -> (
        let then_instrs = rewrite targets labels then_instrs in
        let else_instrs = rewrite targets labels else_instrs in
        match (sink result result_ctyp return_aux then_instrs, sink result result_ctyp return_aux else_instrs) with
        | Some then_instrs, Some else_instrs ->
            I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rewrite targets labels rest
        | _ ->
            I_aux (I_if (condition, then_instrs, else_instrs), if_aux)
            :: I_aux (I_return (V_id (result, result_ctyp)), return_aux)
            :: rewrite targets labels rest
      )
    | I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rest ->
        I_aux (I_if (condition, rewrite targets labels then_instrs, rewrite targets labels else_instrs), if_aux)
        :: rewrite targets labels rest
    | I_aux (I_block instrs, block_aux) :: rest ->
        I_aux (I_block (rewrite targets labels instrs), block_aux) :: rewrite targets labels rest
    | I_aux (I_try_block instrs, block_aux) :: rest ->
        I_aux (I_try_block (rewrite targets labels instrs), block_aux) :: rewrite targets labels rest
    | instr :: rest -> instr :: rewrite targets labels rest
    | [] -> []
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) ->
      let targets = target_counts body in
      let labels = label_counts body in
      let rewritten =
        match structure_terminal_ladder targets labels body with
        | Some structured -> rewrite targets labels structured
        | None -> rewrite targets labels body
      in
      CDEF_aux (CDEF_fundef (id, ret, args, rewritten), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Reconstruct the private forward-label regions used by JIB for ordinary
   expression and statement matches:

     jump invalid case2; arm1; goto finish;
     case2: ...; arm2;
     finish: continuation

   becomes a structured conditional followed by the continuation.  Unlike
   [sink_terminal_stack_returns], this also handles unit-valued matches whose
   join is followed by more work.  Multiple adjacent jumps to the same case
   label are the conjunction of a guarded match arm; their jump conditions are
   combined as a disjunction.  Target and definition counts prove that every
   removed label is private to the reconstructed region. *)
let structure_forward_match_joins (CDEF_aux (aux, def_annot)) =
  let target_counts body =
    let counts = Hashtbl.create 16 in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               ( match aux with
               | I_goto label | I_jump (_, label) ->
                   Hashtbl.replace counts label (1 + Option.value ~default:0 (Hashtbl.find_opt counts label))
               | _ -> ()
               );
               sub
             )
             instr
          )
      )
      body;
    fun label -> Option.value ~default:0 (Hashtbl.find_opt counts label)
  in
  let label_counts body =
    let counts = Hashtbl.create 16 in
    List.iter
      (fun instr ->
        ignore
          (map_instr
             (fun (I_aux (aux, _) as sub) ->
               ( match aux with
               | I_label label ->
                   Hashtbl.replace counts label (1 + Option.value ~default:0 (Hashtbl.find_opt counts label))
               | _ -> ()
               );
               sub
             )
             instr
          )
      )
      body;
    fun label -> Option.value ~default:0 (Hashtbl.find_opt counts label)
  in
  let split_at_label target instrs =
    let rec split reversed = function
      | I_aux (I_label label, _) :: rest when String.equal label target -> Some (List.rev reversed, rest)
      | instr :: rest -> split (instr :: reversed) rest
      | [] -> None
    in
    split [] instrs
  in
  let drop_goto target instrs =
    match List.rev instrs with
    | I_aux (I_goto label, _) :: reversed when String.equal label target -> Some (List.rev reversed)
    | _ -> None
  in
  let branch_at_head = function
    | I_aux (I_jump (condition, alternate), branch_aux) :: rest -> Some (condition, alternate, branch_aux, rest)
    | I_aux (I_if (condition, [I_aux (I_goto alternate, _)], []), branch_aux) :: rest ->
        Some (condition, alternate, branch_aux, rest)
    | I_aux (I_if (condition, [], [I_aux (I_goto alternate, _)]), branch_aux) :: rest ->
        Some (V_call (Bnot, [condition]), alternate, branch_aux, rest)
    | _ -> None
  in
  let split_at_branch instrs =
    let rec split reversed remaining =
      match branch_at_head remaining with
      | Some (condition, alternate, branch_aux, rest) -> Some (List.rev reversed, condition, alternate, branch_aux, rest)
      | None -> (
          match remaining with
          | I_aux ((I_label _ | I_goto _ | I_return _ | I_exit _), _) :: _ -> None
          | instr :: rest -> split (instr :: reversed) rest
          | [] -> None
        )
    in
    split [] instrs
  in
  let consume_same_alternate alternate first_condition instrs =
    let rec consume conditions count remaining =
      match branch_at_head remaining with
      | Some (condition, next_alternate, _, rest) when String.equal alternate next_alternate ->
          consume (condition :: conditions) (count + 1) rest
      | _ ->
          let conditions = List.rev conditions in
          let condition = match conditions with [condition] -> condition | conditions -> V_call (Bor, conditions) in
          (condition, count, remaining)
    in
    consume [first_condition] 1 instrs
  in
  let rec rewrite targets labels instrs =
    let structure_to_join finish_label ladder =
      let rec structure ladder =
        match split_at_branch ladder with
        | Some (condition_prefix, first_condition, alternate_label, branch_aux, after_first_branch) -> (
            let condition, alternate_targets, ladder_tail =
              consume_same_alternate alternate_label first_condition after_first_branch
            in
            match split_at_label alternate_label ladder_tail with
            | Some (primary_with_goto, alternate)
              when labels alternate_label = 1 && targets alternate_label = alternate_targets -> (
                match (drop_goto finish_label primary_with_goto, structure alternate) with
                | Some primary, Some (alternate, gotos) ->
                    Some (condition_prefix @ [I_aux (I_if (condition, alternate, primary), branch_aux)], gotos + 1)
                | _ -> None
              )
            | _ -> None
          )
        | None -> (
            match drop_goto finish_label ladder with Some final_arm -> Some (final_arm, 1) | None -> Some (ladder, 0)
          )
      in
      structure ladder
    in
    match split_at_branch instrs with
    | Some (prefix, first_condition, first_alternate, first_branch_aux, after_first_branch) -> (
        let _condition, alternate_targets, ladder_tail =
          consume_same_alternate first_alternate first_condition after_first_branch
        in
        match split_at_label first_alternate ladder_tail with
        | Some (first_arm_with_goto, after_first_alternate)
          when labels first_alternate = 1 && targets first_alternate = alternate_targets -> (
            match List.rev first_arm_with_goto with
            | I_aux (I_goto finish_label, _) :: _ when labels finish_label = 1 -> (
                match split_at_label finish_label after_first_branch with
                | Some (ladder_before_finish, continuation) -> (
                    (* Preserve the original adjacent guarded-arm jumps here.
                       Their target count is part of the privacy proof and
                       [structure_to_join] combines them itself.  Pass only
                       the match ladder, not the continuation following its
                       join label: the latter is appended exactly once below. *)
                    let complete_ladder =
                      I_aux (I_jump (first_condition, first_alternate), first_branch_aux) :: ladder_before_finish
                    in
                    match structure_to_join finish_label complete_ladder with
                    | Some (structured, gotos) when targets finish_label = gotos ->
                        rewrite targets labels prefix @ structured @ rewrite targets labels continuation
                    | _ -> (
                        match instrs with
                        | I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rest ->
                            I_aux
                              ( I_if (condition, rewrite targets labels then_instrs, rewrite targets labels else_instrs),
                                if_aux
                              )
                            :: rewrite targets labels rest
                        | instr :: rest -> instr :: rewrite targets labels rest
                        | [] -> []
                      )
                  )
                | None -> (
                    match instrs with instr :: rest -> instr :: rewrite targets labels rest | [] -> []
                  )
              )
            | _ -> (
                match instrs with instr :: rest -> instr :: rewrite targets labels rest | [] -> []
              )
          )
        | _ -> (
            match instrs with
            | I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rest ->
                I_aux (I_if (condition, rewrite targets labels then_instrs, rewrite targets labels else_instrs), if_aux)
                :: rewrite targets labels rest
            | instr :: rest -> instr :: rewrite targets labels rest
            | [] -> []
          )
      )
    | None -> (
        match instrs with
        | I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rest ->
            I_aux (I_if (condition, rewrite targets labels then_instrs, rewrite targets labels else_instrs), if_aux)
            :: rewrite targets labels rest
        | I_aux (I_block block, block_aux) :: rest ->
            I_aux (I_block (rewrite targets labels block), block_aux) :: rewrite targets labels rest
        | I_aux (I_try_block block, block_aux) :: rest ->
            I_aux (I_try_block (rewrite targets labels block), block_aux) :: rewrite targets labels rest
        | instr :: rest -> instr :: rewrite targets labels rest
        | [] -> []
      )
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) ->
      let targets = target_counts body in
      let labels = label_counts body in
      CDEF_aux (CDEF_fundef (id, ret, args, rewrite targets labels body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* C can elide the copy of a named aggregate local only when every return of
   that value reaches one named return statement.  Late return sinking makes
   the common Sail shape

     if (condition) return transform(result);
     return result;

   readable, but Clang correctly reports that the two returns disable NRVO.
   Restore the equally direct single-return form by assigning the transformed
   value back to the already-initialized stack aggregate.  The inverse shape
   is handled only when the selected arm is exactly [return result], so moving
   the fallthrough computation under the inverted guard cannot discard work.
   Scalar returns are deliberately left alone. *)
let consolidate_named_aggregate_returns ctx (CDEF_aux (aux, def_annot)) =
  let locals = ref NameSet.empty in
  let is_aggregate = function
    | CT_struct _ | CT_variant _ | CT_tup _ | CT_fvector _ -> true
    | ctyp -> is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp || is_c_repr_fixed_bytes ctyp
  in
  let assign_return_to result result_ctyp = function
    | I_aux (I_return value, instr_aux) when ctyp_equal (cval_ctyp value) result_ctyp ->
        Some (I_aux (I_copy (CL_id (result, result_ctyp), value), instr_aux), instr_aux)
    | I_aux (I_funcall (CR_one (CL_id (Return _, return_ctyp)), extern, callee, args), instr_aux)
      when ctyp_equal return_ctyp result_ctyp ->
        Some (I_aux (I_funcall (CR_one (CL_id (result, result_ctyp)), extern, callee, args), instr_aux), instr_aux)
    | _ -> None
  in
  let assign_terminal_return result result_ctyp branch =
    match List.rev branch with
    | terminal :: reversed -> (
        match assign_return_to result result_ctyp terminal with
        | Some (assignment, _) -> Some (List.rev (assignment :: reversed))
        | None -> None
      )
    | [] -> None
  in
  let exact_named_return = function
    | [I_aux (I_return (V_id (result, result_ctyp)), return_aux)] -> Some (result, result_ctyp, return_aux)
    | _ -> None
  in
  let rec rewrite = function
    | I_aux (I_if (condition, then_instrs, []), if_aux)
      :: I_aux (I_return (V_id (result, result_ctyp)), return_aux)
      :: rest
      when NameSet.mem result !locals && is_aggregate result_ctyp && is_stack_ctyp ctx result_ctyp -> (
        let then_instrs = rewrite then_instrs in
        match assign_terminal_return result result_ctyp then_instrs with
        | Some then_instrs ->
            I_aux (I_if (condition, then_instrs, []), if_aux)
            :: I_aux (I_return (V_id (result, result_ctyp)), return_aux)
            :: rewrite rest
        | None ->
            I_aux (I_if (condition, then_instrs, []), if_aux)
            :: I_aux (I_return (V_id (result, result_ctyp)), return_aux)
            :: rewrite rest
      )
    | I_aux (I_if (condition, then_instrs, []), if_aux) :: terminal :: rest -> (
        let then_instrs = rewrite then_instrs in
        match exact_named_return then_instrs with
        | Some (result, result_ctyp, return_aux)
          when NameSet.mem result !locals && is_aggregate result_ctyp && is_stack_ctyp ctx result_ctyp -> (
            match assign_return_to result result_ctyp terminal with
            | Some (assignment, _) ->
                I_aux (I_if (V_call (Bnot, [condition]), [assignment], []), if_aux)
                :: I_aux (I_return (V_id (result, result_ctyp)), return_aux)
                :: rewrite rest
            | None -> I_aux (I_if (condition, then_instrs, []), if_aux) :: terminal :: rewrite rest
          )
        | _ -> I_aux (I_if (condition, then_instrs, []), if_aux) :: terminal :: rewrite rest
      )
    | I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rest ->
        I_aux (I_if (condition, rewrite then_instrs, rewrite else_instrs), if_aux) :: rewrite rest
    | I_aux (I_block instrs, block_aux) :: rest -> I_aux (I_block (rewrite instrs), block_aux) :: rewrite rest
    | I_aux (I_try_block instrs, block_aux) :: rest -> I_aux (I_try_block (rewrite instrs), block_aux) :: rewrite rest
    | instr :: rest -> instr :: rewrite rest
    | [] -> []
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) ->
      List.iter
        (fun instr ->
          ignore
            (map_instr
               (fun (I_aux (aux, _) as sub) ->
                 ( match aux with
                 | I_decl (_, local) | I_init (_, local, _) -> locals := NameSet.add local !locals
                 | _ -> ()
                 );
                 sub
               )
               instr
            )
        )
        body;
      CDEF_aux (CDEF_fundef (id, ret, args, rewrite body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

let is_noreturn_call ctx = function
  | I_aux (I_funcall (_, extern_info, callee, args), _) -> (
      let callee_id = fst callee in
      let name =
        match extern_info with
        | Extern _ -> string_of_id callee_id
        | Call _ when ctx_is_extern callee_id ctx -> ctx_get_extern callee_id ctx
        | Call _ -> string_of_id callee_id
      in
      String.equal name "fatal_error"
      || (String.equal name "sail_assert" || String.equal name "__sail_fixed_assert")
         && match args with V_lit (VL_bool false, _) :: _ -> true | _ -> false
    )
  | _ -> false

(* [fatal_error] and a statically-failing Sail assertion are noreturn
   boundaries.  Match lowering may leave an [I_exit] or additional join
   scaffolding after either call.  Nothing in the same lexical instruction
   sequence is reachable once the call executes, so truncate it in typed JIB
   instead of emitting a misleading [sail_match_failure].  Nested branches are
   rewritten independently; a terminating call in only one arm therefore
   cannot discard the other arm's continuation. *)
let prune_after_noreturn_call ctx (CDEF_aux (aux, def_annot)) =
  let rec rewrite = function
    | [] -> []
    | instr :: _ when is_noreturn_call ctx instr -> [instr]
    | I_aux (I_if (condition, then_instrs, else_instrs), if_aux) :: rest ->
        I_aux (I_if (condition, rewrite then_instrs, rewrite else_instrs), if_aux) :: rewrite rest
    | I_aux (I_block instrs, block_aux) :: rest -> I_aux (I_block (rewrite instrs), block_aux) :: rewrite rest
    | I_aux (I_try_block instrs, block_aux) :: rest -> I_aux (I_try_block (rewrite instrs), block_aux) :: rewrite rest
    | instr :: rest -> instr :: rewrite rest
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

let propagate_pure_copies (CDEF_aux (aux, def_annot)) =
  let rec trivial = function
    | V_id _ | V_member _ | V_lit _ -> true
    | V_tuple values -> List.for_all trivial values
    | _ -> false
  in
  let preserve_assignment_conversion target_ctyp value =
    let source_ctyp = cval_ctyp value in
    if ctyp_equal source_ctyp target_ctyp then Some value
    else (
      match (target_ctyp, source_ctyp) with
      | CT_fuint width, (CT_fuint _ | CT_fint _ | CT_fbits _ | CT_constant _) -> Some (V_call (Unsigned width, [value]))
      | CT_fint width, (CT_fuint _ | CT_fint _ | CT_fbits _ | CT_constant _) -> Some (V_call (Signed width, [value]))
      | _ -> None
    )
  in
  let contains_label instr =
    let found = ref false in
    ignore
      (map_instr
         (fun (I_aux (aux, _) as sub) ->
           (match aux with I_label _ -> found := true | _ -> ());
           sub
         )
         instr
      );
    !found
  in
  let rewrite_lists locals instrs =
    (* A declaration may precede the assignment that gives a temporary its
       first value because JIB preserves the Sail expression's outer scope.
       The intervening instructions are retained in place: finding the copy
       only lets the ordinary copy-propagation proof see the same web it would
       see if declaration and assignment had been adjacent.  Do not cross a
       label or any reference to the declared name. *)
    let rec first_copy name decl_ctyp rev_gap = function
      | (I_aux (I_copy (CL_id (copy_name, copy_ctyp), cval), _) as copy) :: rest
        when Name.compare name copy_name = 0 && ctyp_equal decl_ctyp copy_ctyp ->
          Some (List.rev rev_gap, copy, cval, rest)
      | instr :: rest when (not (contains_label instr)) && not (NameSet.mem name (instr_ids ~direct:false instr)) ->
          first_copy name decl_ctyp (instr :: rev_gap) rest
      | _ -> None
    in
    let rec scan acc = function
      | (I_aux (I_decl (decl_ctyp, ((Name _ | Gen _) as x)), _) as decl) :: tail -> (
          match first_copy x decl_ctyp [] tail with
          | None -> scan (decl :: acc) tail
          | Some (gap, copy, cval, rest) -> (
              match preserve_assignment_conversion decl_ctyp cval with
              | None -> scan (decl :: acc) tail
              | Some propagated_cval ->
                  let roots = instr_reads ~direct:true copy in
                  let reads_of instr = if instr_references ~read:x ~direct:false instr then 1 else 0 in
                  let read_count = List.fold_left (fun n instr -> n + reads_of instr) 0 rest in
                  let written_later name =
                    List.exists (fun instr -> instr_references ~write:name ~direct:false instr) rest
                  in
                  let label_before_last_read =
                    let rec check remaining_reads = function
                      | [] -> false
                      | _ when remaining_reads <= 0 -> false
                      | instr :: rest -> contains_label instr || check (remaining_reads - reads_of instr) rest
                    in
                    check read_count rest
                  in
                  let safe =
                    NameSet.subset roots locals
                    && (not (NameSet.exists written_later roots))
                    && (not (written_later x))
                    && (not label_before_last_read)
                    && (read_count = 1 || trivial propagated_cval)
                  in
                  if not safe then scan (decl :: acc) tail
                  else if read_count = 0 then scan (List.rev_append gap acc) rest
                  else (
                    let substitute = function
                      | V_id (name, _) when Name.compare name x = 0 -> propagated_cval
                      | other -> other
                    in
                    let simplify_tuple_projection = function
                      | V_tuple_member (V_tuple values, length, index)
                        when List.length values = length && index >= 0 && index < length ->
                          List.nth values index
                      | value -> value
                    in
                    scan (List.rev_append gap acc)
                      (List.map
                         (fun instr -> map_instr_cval substitute instr |> map_instr_cval simplify_tuple_projection)
                         rest
                      )
                  )
            )
        )
      | instr :: rest -> scan (instr :: acc) rest
      | [] -> List.rev acc
    in
    scan [] instrs
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) ->
      (* A write does not make its destination a local: Sail registers are
         ordinary JIB names too, and a function may assign one before taking a
         snapshot of it.  Treating every written name as local allowed the
         snapshot to be substituted across a later call which mutated the
         register.  Only arguments and names with an actual body declaration
         have value lifetimes that this local data-flow proof can track. *)
      let locals = ref (NameSet.of_list args) in
      List.iter
        (fun instr ->
          ignore
            (map_instr
               (fun (I_aux (aux, _) as sub) ->
                 ( match aux with
                 | I_decl (_, name) | I_init (_, name, _) -> locals := NameSet.add name !locals
                 | _ -> ()
                 );
                 sub
               )
               instr
            )
        )
        body;
      let rec fixpoint n body =
        let rewritten = List.map (map_instrs (rewrite_lists !locals)) body in
        let rewritten = rewrite_lists !locals rewritten in
        if n = 0 then rewritten else fixpoint (n - 1) rewritten
      in
      let body = fixpoint 2 body in
      CDEF_aux (CDEF_fundef (id, ret, args, body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Declaration fusion is intentionally the final producer of local
   declarations.  Doing it before copy propagation and terminal-return
   sinking obscures the declaration/copy patterns those semantic simplifiers
   consume.  A final [fold_copy_conversions] below consumes any
   initialization/return pair created here. *)
let initialize_stack_locals (CDEF_aux (aux, def_annot)) =
  let initialization_value target_ctyp value =
    let source_ctyp = cval_ctyp value in
    if ctyp_equal source_ctyp target_ctyp then Some value
    else (
      match (target_ctyp, source_ctyp) with
      | CT_fuint width, (CT_fuint _ | CT_fint _ | CT_constant _) -> Some (V_call (Unsigned width, [value]))
      | CT_fint width, (CT_fuint _ | CT_fint _ | CT_constant _) -> Some (V_call (Signed width, [value]))
      | _ -> None
    )
  in
  let rewrite_lists instrs =
    let rec rewrite = function
      | I_aux (I_decl (decl_ctyp, destination), decl_aux)
        :: I_aux (I_copy (CL_id (assigned, copy_ctyp), value), copy_aux)
        :: rest
        when Name.compare destination assigned = 0 && ctyp_equal decl_ctyp copy_ctyp -> (
          match initialization_value decl_ctyp value with
          | Some value -> I_aux (I_init (decl_ctyp, destination, Init_cval value), decl_aux) :: rewrite rest
          | None ->
              I_aux (I_decl (decl_ctyp, destination), decl_aux)
              :: I_aux (I_copy (CL_id (assigned, copy_ctyp), value), copy_aux)
              :: rewrite rest
        )
      | instr :: rest -> instr :: rewrite rest
      | [] -> []
    in
    rewrite instrs
  in
  let rewrite_body body = List.map (map_instrs rewrite_lists) body |> rewrite_lists in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Normalize the boolean cvals exposed by copy propagation before rendering
   structured control flow.  This is intentionally a small, proof-obvious
   algebra over C's bool-valued JIB operations: it neither duplicates nor
   reorders an operand.

     !(!condition)  -> condition
     condition == true / true == condition -> condition
     condition == false / false == condition -> !condition
     condition != false / false != condition -> condition
     condition != true / true != condition -> !condition
     false || condition / condition || false -> condition
     true && condition / condition && true -> condition

   A leading negation on an if is removed by exchanging its arms.  Besides
   producing the positive form a Sail reader expects, this also lets the
   empty-arm renderer avoid introducing a second negation. *)
let simplify_boolean_control_flow (CDEF_aux (aux, def_annot)) =
  let bool_literal expected = function
    | V_lit (VL_bool actual, CT_bool) when Bool.equal expected actual -> true
    | _ -> false
  in
  let negate value = match value with V_call (Bnot, [inner]) -> inner | _ -> V_call (Bnot, [value]) in
  let literal value = V_lit (VL_bool value, CT_bool) in
  let simplify_boolean_operator operator ~identity ~annihilator values =
    if List.exists (bool_literal annihilator) values then literal annihilator
    else (
      match List.filter (fun value -> not (bool_literal identity value)) values with
      | [] -> literal identity
      | [value] -> value
      | values -> V_call (operator, values)
    )
  in
  let simplify_comparison equal left right =
    let with_literal value literal =
      if not (ctyp_equal (cval_ctyp value) CT_bool) then None
      else if bool_literal true literal then Some (if equal then value else negate value)
      else if bool_literal false literal then Some (if equal then negate value else value)
      else None
    in
    match with_literal left right with Some value -> Some value | None -> with_literal right left
  in
  let simplify = function
    | V_call (Bnot, [V_lit (VL_bool value, CT_bool)]) -> literal (not value)
    | V_call (Bnot, [V_call (Bnot, [value])]) -> value
    | V_call (Bor, values) -> simplify_boolean_operator Bor ~identity:false ~annihilator:true values
    | V_call (Band, values) -> simplify_boolean_operator Band ~identity:true ~annihilator:false values
    | V_call (Eq, [left; right]) as comparison -> (
        match simplify_comparison true left right with Some value -> value | None -> comparison
      )
    | V_call (Neq, [left; right]) as comparison -> (
        match simplify_comparison false left right with Some value -> value | None -> comparison
      )
    | value -> value
  in
  let rewrite_if = function
    | I_aux (I_if (V_call (Bnot, [condition]), then_instrs, else_instrs), annot) ->
        I_aux (I_if (condition, else_instrs, then_instrs), annot)
    | instr -> instr
  in
  let rewrite_body body =
    let rec fixpoint n body =
      let rewritten = List.map (map_instr_cval simplify) body |> List.map (map_instr rewrite_if) in
      if n = 0 || rewritten = body then rewritten else fixpoint (n - 1) rewritten
    in
    fixpoint 2 body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* JIB's native integer types retain useful range information after dependent
   Sail types have been specialized. Use only ranges that follow directly
   from those representations, literals, and a positive constant remainder;
   this is enough to remove checked-conversion guards that have become
   impossible without rerunning the source-level prover in the C backend. *)
let integer_ctyp_bounds = function
  | CT_fuint width -> Some (Big_int.zero, max_uint width)
  | CT_fint width -> Some (min_int width, max_int width)
  | CT_fbits width -> Some (Big_int.zero, max_uint width)
  | ctyp when is_c_repr_u128 ctyp -> Some (Big_int.zero, max_uint 128)
  | ctyp when is_c_repr_u256 ctyp -> Some (Big_int.zero, max_uint 256)
  | ctyp when is_c_repr_u320 ctyp -> Some (Big_int.zero, max_uint 320)
  | CT_constant value -> Some (value, value)
  | _ -> None

let bit_literal_integer bits =
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

let rec integer_literal_value = function
  | V_lit (VL_int value, _) -> Some value
  | V_lit (VL_bits bits, _) -> bit_literal_integer bits
  | V_call ((Unsigned _ | Zero_extend _), [value]) -> integer_literal_value value
  | _ -> None

let rec integer_cval_bounds = function
  | V_lit (VL_int value, _) -> Some (value, value)
  | V_lit (VL_bits bits, _) -> Option.map (fun value -> (value, value)) (bit_literal_integer bits)
  | V_call ((Unsigned width | Zero_extend width), [value]) -> (
      match integer_cval_bounds value with
      | Some (lower, upper) when Big_int.greater_equal lower Big_int.zero ->
          Some (lower, Big_int.min upper (max_uint width))
      | _ -> Some (Big_int.zero, max_uint width)
    )
  | V_call (Signed width, [_]) -> Some (min_int width, max_int width)
  | V_call (Bvand, [left; right]) -> (
      match (integer_literal_value left, integer_literal_value right) with
      | _, Some mask when Big_int.greater_equal mask Big_int.zero -> integer_mask_bounds left mask
      | Some mask, _ when Big_int.greater_equal mask Big_int.zero -> integer_mask_bounds right mask
      | _ -> integer_ctyp_bounds (cval_ctyp left)
    )
  | V_call ((Imod | Proven_imod), [left; right]) -> integer_remainder_bounds left right
  | V_call (Mixed_proven_imod (_, _), [left; right]) -> integer_remainder_bounds left right
  | value -> integer_ctyp_bounds (cval_ctyp value)

and integer_mask_bounds value mask =
  match integer_cval_bounds value with
  | Some (lower, upper) when Big_int.greater_equal lower Big_int.zero -> Some (Big_int.zero, Big_int.min upper mask)
  | _ -> Some (Big_int.zero, mask)

and integer_remainder_bounds left right =
  match (integer_cval_bounds left, integer_cval_bounds right) with
  | Some (left_lower, left_upper), Some (modulus_lower, modulus_upper)
    when Big_int.equal modulus_lower modulus_upper && Big_int.greater modulus_lower Big_int.zero ->
      let magnitude = Big_int.pred modulus_lower in
      if Big_int.less_equal Big_int.zero left_lower then Some (Big_int.zero, Big_int.min left_upper magnitude)
      else if Big_int.less_equal left_upper Big_int.zero then
        Some (Big_int.max left_lower (Big_int.negate magnitude), Big_int.zero)
      else Some (Big_int.negate magnitude, magnitude)
  | _ -> None

let integer_cval_fits lower upper value =
  match integer_cval_bounds value with
  | Some (value_lower, value_upper) -> Big_int.less_equal lower value_lower && Big_int.less_equal value_upper upper
  | None -> false

let simplify_bounded_integer_predicates (CDEF_aux (aux, def_annot)) =
  let bounds = integer_cval_bounds in
  let comparison_result op (left_lower, left_upper) (right_lower, right_upper) =
    match op with
    | Ilt when Big_int.less left_upper right_lower -> Some true
    | Ilt when Big_int.greater_equal left_lower right_upper -> Some false
    | Igt when Big_int.greater left_lower right_upper -> Some true
    | Igt when Big_int.less_equal left_upper right_lower -> Some false
    | Ilteq when Big_int.less_equal left_upper right_lower -> Some true
    | Ilteq when Big_int.greater left_lower right_upper -> Some false
    | Igteq when Big_int.greater_equal left_lower right_upper -> Some true
    | Igteq when Big_int.less left_upper right_lower -> Some false
    | Eq when Big_int.less left_upper right_lower || Big_int.greater left_lower right_upper -> Some false
    | Eq
      when Big_int.equal left_lower left_upper && Big_int.equal right_lower right_upper
           && Big_int.equal left_lower right_lower ->
        Some true
    | Neq when Big_int.less left_upper right_lower || Big_int.greater left_lower right_upper -> Some true
    | Neq
      when Big_int.equal left_lower left_upper && Big_int.equal right_lower right_upper
           && Big_int.equal left_lower right_lower ->
        Some false
    | _ -> None
  in
  let simplify = function
    | V_call (((Ilt | Igt | Ilteq | Igteq | Eq | Neq) as op), [left; right]) as comparison -> (
        match (bounds left, bounds right) with
        | Some left_bounds, Some right_bounds -> (
            match comparison_result op left_bounds right_bounds with
            | Some result -> V_lit (VL_bool result, CT_bool)
            | None -> comparison
          )
        | _ -> comparison
      )
    | value -> value
  in
  let rewrite_body body =
    let rec fixpoint n body =
      let rewritten = List.map (map_instr_cval simplify) body in
      if n = 0 || rewritten = body then rewritten else fixpoint (n - 1) rewritten
    in
    fixpoint 2 body
  in
  match aux with
  | CDEF_fundef (id, ret, args, body) -> CDEF_aux (CDEF_fundef (id, ret, args, rewrite_body body), def_annot)
  | _ -> CDEF_aux (aux, def_annot)

(* Top-level letbinds whose bound globals are never read do not deserve a
   create_letbind initializer or storage. Sail top-level lets are pure, so
   dropping an unread one cannot change observable behavior. Liveness is
   transitive: a letbind read only by another letbind's initializer stays
   only if that letbind is itself live. Returns the filtered definitions and
   the surviving letbind numbers. *)
let optimize_dead_letbinds = ref false

let remove_dead_letbinds cdefs =
  let letbind_names =
    List.filter_map
      (function
        | CDEF_aux (CDEF_let (number, bindings, _), _) ->
            Some (number, NameSet.of_list (List.map (fun (id, _) -> name id) bindings))
        | _ -> None
        )
      cdefs
  in
  let letbind_reads =
    List.filter_map
      (function
        | CDEF_aux (CDEF_let (number, _, instrs), _) ->
            Some
              ( number,
                List.fold_left
                  (fun acc instr -> NameSet.union acc (instr_reads ~direct:false instr))
                  NameSet.empty instrs
              )
        | _ -> None
        )
      cdefs
  in
  let base_reads =
    List.fold_left
      (fun acc cdef ->
        match cdef with
        | CDEF_aux (CDEF_let _, _) -> acc
        | CDEF_aux ((CDEF_fundef (_, _, _, instrs) | CDEF_startup (_, instrs) | CDEF_finish (_, instrs)), _) ->
            List.fold_left (fun acc instr -> NameSet.union acc (instr_reads ~direct:false instr)) acc instrs
        | CDEF_aux (CDEF_register (_, _, instrs), _) ->
            List.fold_left (fun acc instr -> NameSet.union acc (instr_reads ~direct:false instr)) acc instrs
        | _ -> acc
      )
      NameSet.empty cdefs
  in
  let live_of reads =
    List.filter_map (fun (number, names) -> if NameSet.disjoint names reads then None else Some number) letbind_names
  in
  let rec fixpoint live =
    let reads =
      List.fold_left
        (fun acc (number, reads) -> if List.mem number live then NameSet.union acc reads else acc)
        base_reads letbind_reads
    in
    let live' = live_of reads in
    if List.length live' = List.length live then live' else fixpoint live'
  in
  let live = fixpoint (live_of base_reads) in
  let cdefs =
    List.filter (function CDEF_aux (CDEF_let (number, _, _), _) -> List.mem number live | _ -> true) cdefs
  in
  (cdefs, live)

let optimize ~have_rts ~specialize_c ~optimized_model ctx recursive_functions cdefs =
  let nothing cdefs = cdefs in
  cdefs
  |> (if !optimize_unit_results then List.map (discard_unread_stack_results ctx) else nothing)
  |> (if !optimize_pure_copies then List.map (flatten_unique_stack_blocks ctx) else nothing)
  |> (if !optimize_pure_copies then List.map (fold_stack_aggregate_construction ctx) else nothing)
  |> (if !optimize_pure_copies then List.map collapse_short_circuit_booleans else nothing)
  |> (if !optimize_pure_copies then List.map merge_repeated_conditional_branches else nothing)
  |> (if !optimize_pure_copies then List.map simplify_bounded_integer_predicates else nothing)
  |> (if !optimize_pure_copies then List.map prune_constant_branches else nothing)
  |> (if !optimize_pure_copies then List.map (flatten_terminal_guards ctx) else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map fold_copy_conversions else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_alias then List.concat_map remove_alias else nothing)
  |> (if !optimize_alias then combine_variables ctx else nothing)
  |> (if !optimize_pure_copies then List.map fold_copy_conversions else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map (fold_stack_aggregate_construction ctx) else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map collapse_short_circuit_booleans else nothing)
  |> (if !optimize_pure_copies then List.map (flatten_unique_stack_blocks ctx) else nothing)
  |> (if !optimize_pure_copies then List.map collapse_short_circuit_booleans else nothing)
  |> (if !optimize_pure_copies then List.map (flatten_terminal_guards ctx) else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map (fold_stack_aggregate_construction ctx) else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map collapse_short_circuit_booleans else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map fold_copy_conversions else nothing)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  (* We need the runtime to initialize hoisted allocations *)
  |> ( if !optimize_hoist_allocations && have_rts then List.concat_map (hoist_allocations recursive_functions)
       else nothing
     )
  |> (if specialize_c then drop_redundant_to_bytes_mask else nothing)
  |> remove_stack_clears ctx
  |> (if !optimize_pure_copies then List.map collapse_short_circuit_booleans else nothing)
  |> (if !optimize_pure_copies then List.map simplify_boolean_control_flow else nothing)
  |> (if !optimize_pure_copies then List.map fold_copy_conversions else nothing)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map fold_copy_conversions else nothing)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_unit_results then List.map (discard_unread_stack_results ctx) else nothing)
  |> (if !optimize_unit_results then List.map (erase_unit_scaffolding ctx) else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map simplify_boolean_control_flow else nothing)
  |> (if !optimize_pure_copies then List.map merge_repeated_conditional_branches else nothing)
  |> (if !optimize_pure_copies then List.map simplify_bounded_integer_predicates else nothing)
  |> (if !optimize_pure_copies then List.map prune_constant_branches else nothing)
  |> (if !optimize_pure_copies then List.map (flatten_terminal_guards ctx) else nothing)
  |> (if !optimize_unit_results then List.map remove_fallthrough_gotos else nothing)
  |> (if !optimize_unit_results then List.map (return_from_terminal_unit_label ctx) else nothing)
  |> (if !optimize_pure_copies then List.map return_from_terminal_stack_label else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map simplify_boolean_control_flow else nothing)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  (* The preceding propagation can expose a narrow tuple literal only after
     the earlier aggregate passes have run. Normalize its field widening in
     typed JIB, then sink the exact result before local initialization makes
     the remaining match labels lifetime-sensitive in emitted C. *)
  |> (if !optimize_pure_copies then List.map (fold_stack_aggregate_construction ctx) else nothing)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map simplify_boolean_control_flow else nothing)
  |> (if !optimize_pure_copies then List.map merge_repeated_conditional_branches else nothing)
  |> (if !optimize_pure_copies then List.map initialize_stack_locals else nothing)
  |> (if !optimize_pure_copies then List.map fold_copy_conversions else nothing)
  |> (if !optimize_pure_copies then List.map structure_forward_match_joins else nothing)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  (* Late return sinking creates new terminal branches after the earlier guard
     cleanup.  Flatten those only after declarations and conversions have
     reached their final form, so generated C never retains an [else] merely
     because its sibling became a direct return late in this pipeline. *)
  |> (if !optimize_pure_copies then List.map (flatten_terminal_guards ctx) else nothing)
  (* Flattening a terminal guard can expose one last match ladder whose join
     was previously nested in the surviving branch.  Re-run return sinking so
     that match arms return their values directly before C emission. *)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing)
  |> (if !optimize_pure_copies then List.map propagate_pure_copies else nothing)
  |> (if !optimize_pure_copies then List.map structure_forward_match_joins else nothing)
  |> (if !optimize_pure_copies then List.map sink_terminal_stack_returns else nothing)
  |> (if !optimize_pure_copies then List.map (flatten_terminal_guards ctx) else nothing)
  |> (if !optimize_pure_copies then List.map (consolidate_named_aggregate_returns ctx) else nothing)
  |> List.map (prune_after_noreturn_call ctx)
  |> (if !optimize_unit_results then List.map (discard_unread_stack_results ctx) else nothing)
  |> if !optimize_pure_copies then List.map simplify_pure_copy_scaffolding else nothing

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
  (* A static type helper selected by a generated function body.  Modular
     emission uses the symbolic helper name to keep the definition only in
     translation units whose typed JIB lowering actually selected it. *)
  | DemandedStaticFunctionDefinition of string * document

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
  val c_repr_fixed_bytes_u64_lanes : int Bindings.t
  val c_repr_fixed_bytes_u64_lane_alias_lengths : int list
  val c_repr_fixed_bytes_names : (int * string) list
  val c_static_evaluators : string Bindings.t
  val specialize_c : bool
  val require_bounded_int : bool
  val const_match_tables : bool
  val specialization_plan_json : string option
  val specialization_plan_human : string option
  val specialization_obligations_lean : string option
  val specialization_obligations_coq : string option
  val optimized_model : bool
  val register_file : bool
  val register_file_thread : bool
  val register_file_excluded_modules : string list
  val preserved_functions : IdSet.t
  val external_types : string Bindings.t
  val external_type_names : string Bindings.t
  val byte_pointer_fields : (id * id * string) list
  val byte_pointer_types : string Bindings.t
  val byte_pointer_signatures : (string option list * string option) Bindings.t
  val fixed_bytes_signatures : (int option list * int option) Bindings.t
  val fixed_bytes_u64_lanes_signatures : (int option list * int option) Bindings.t
  val package_name : string
  val cpp : bool
  val cpp_class_name : string
  val cpp_namespace : string
  val cpp_derive_from : string option
end

module Codegen (Config : CODEGEN_CONFIG) = struct
  open Printf

  type c_module = { name : string; file_stem : string; files : string list; requires : string list }

  type c_module_output = { name : string; file_stem : string; header : string; implementation : string }

  let requested_modules : (string * c_module list) option ref = ref None
  let generated_modules : c_module_output list option ref = ref None
  let generated_base_header : string option ref = ref None
  let generated_support_header : string option ref = ref None
  let generated_module_emitter : (c_module_output -> unit) option ref = ref None
  let emitted_external_functions = ref Util.StringSet.empty
  let emitted_external_declarations = ref Util.StringSet.empty
  let current_static_helper_demands = ref Util.StringSet.empty
  let static_equality_declarations : (string * document) list ref = ref []
  let static_equality_declaration_names = ref Util.StringSet.empty
  let function_parameter_names : string list Bindings.t ref = ref Bindings.empty

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

        (* In no-mangle mode a forbidden name (a gensym containing '#' or
           '.', a C keyword collision) is sanitized into a readable C
           identifier instead of z-encoded; the generator's variant counter
           resolves any collisions. *)
        let readable_sanitize s =
          let buf = Buffer.create (String.length s + 1) in
          String.iter
            (fun c ->
              match c with
              | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> Buffer.add_char buf c
              | _ -> Buffer.add_char buf '_'
            )
            s;
          let s = Buffer.contents buf in
          let s = if s = "" then "tmp" else s in
          match s.[0] with '0' .. '9' -> "tmp_" ^ s | _ -> s

        let mangle () s =
          if Config.no_mangle && String.equal s "main" then "zmain"
          else if Config.no_mangle then (
            let sanitized = readable_sanitize s in
            (* A name can be forbidden without containing invalid characters
               (C keywords, reserved prefixes); mangling must always rename. *)
            if String.equal sanitized s then sanitized ^ "_" else sanitized
          )
          else Util.zencode_string s

        let variant s = function 0 -> s | n -> s ^ string_of_int n

        let overrides = Config.overrides
      end)
      ()

  let sgen_id id = NameGen.to_string () id

  let sgen_uid (id, ctyps) =
    match ctyps with
    | [] -> NameGen.to_string () id
    | _ -> NameGen.translate () (string_of_id id ^ "#" ^ Util.string_of_list "_" string_of_ctyp ctyps)

  (* == --c-register-file ====================================================
     With [Config.register_file] the model registers are emitted as members of
     one file-scope [struct model_registers] instead of individual C globals.
     Rationale: the zkVM guests build with -mcmodel=medany -mno-relax and
     RISC-V gcc has no section anchors, so every distinct global referenced by
     a function pays its own auipc/addi address materialization; members of one
     struct share a single base address.

     The mode is semantics-neutral:
     - Generated code spells every member register access as
       [model_registers.NAME] directly (via [sgen_name]).  Sail rejects local
       bindings and parameters that shadow a register ("Cannot shadow register
       in pattern"), so inside generated bodies any [Name] matching a register
       identifier is necessarily a register access.
     - Hand-written FFI keeps compiling unchanged: the anchor module header
       (the last generated module that declares a member register; every
       module header transitively includes its predecessors, and any C file
       that could previously see a register's extern declaration therefore
       also sees the anchor block) defines one object-like macro per member,
       [#define NAME (model_registers.NAME)].  The member token after '.' in
       the replacement list is the macro currently being expanded and is not
       rescanned (C11 6.10.3.4 "blue paint"), so the self-reference is safe.
       Generated translation units suppress these aliases by defining
       [<PACKAGE>_REGISTER_FILE_DIRECT] before including the umbrella header;
       otherwise the macros would corrupt the direct member spelling
       (model_registers.NAME would rescan NAME) and could capture generated
       struct-field names.
     - Registers declared in [Config.register_file_excluded_modules] (for
       example the EVM_DEBUG-gated host/debug_enabled module, whose registers
       are read by hand-written platform code through its own extern
       declarations without including the generated headers) keep today's
       plain-global emission so their linker symbols survive. *)
  let register_file_variable = "model_registers"

  (* Measured-hot interpreter registers are placed first so they share the
     smallest offsets from the register-file base (and one cache line where
     possible).  This is a simple name-based priority list; names that do not
     exist in the model are skipped, and all remaining members follow in
     source declaration order. *)
  let register_file_hot_priority =
    ["pc"; "gas_remaining"; "state_gas_remaining"; "state_gas_spilled"; "frame_status"; "call_depth"; "frame_refund"]

  let register_file_member_ids = ref IdSet.empty
  let register_file_members : (name * ctyp) list ref = ref []
  let register_file_anchor_index = ref (-1)

  (* == --c-register-file-thread =============================================
     Under -mcmodel=medany -mno-relax even the single shared register-file
     base still costs one auipc/addi materialization per function (sometimes
     re-materialized per branch).  With [Config.register_file_thread] every
     generated function whose own body accesses a member register instead
     takes the base as a leading parameter [struct model_registers *const
     regs] and spells accesses [regs->NAME]: the base arrives in an argument
     register and each access is a single offset load/store.

     - The footprint is per function and syntactic: a function is threaded
       exactly when its own JIB body (including nested blocks, but not its
       callees) reads or writes a member register.  Call sites forward their
       own [regs] when the caller is threaded and pass [&model_registers]
       otherwise, so the pointer always equals the global's address and
       aliasing with extern/FFI accesses through the compatibility macros is
       trivially coherent.
     - Entry points reached from hand-written FFI (zmain, every --c-preserve
       function, and initialize_registers/__InitConfig called from
       model_init) keep their existing signatures; they are the region roots
       that materialize the base themselves.
     - The plain parameter name [regs] is reserved in [Config.reserved_words]
       while the mode is on, so generated names can never collide with it.
     - Heap-return functions order the parameter before the return pointer:
       [f(regs, *rop, args...)]. *)
  let register_file_param = "regs"
  let register_file_thread_parameter = "struct " ^ register_file_variable ^ " *const " ^ register_file_param
  let register_file_threaded_functions = ref IdSet.empty
  let current_function_threaded = ref false

  let register_file_threaded_function id = Config.register_file_thread && IdSet.mem id !register_file_threaded_functions

  let register_file_member = function
    | Name (id, _) -> Config.register_file && IdSet.mem id !register_file_member_ids
    | _ -> false

  let register_file_compat_guard () = String.uppercase_ascii Config.package_name ^ "_REGISTER_FILE_DIRECT"

  let sgen_name =
    let ssa_num n = if n = -1 then "" else "/" ^ string_of_int n in
    function
    | Gen (v1, v2, n, source_name, _) when Config.no_mangle ->
        let source_name = Option.value ~default:"tmp" source_name in
        NameGen.translate () (sprintf "%s#%d.%d" source_name v1 v2) ^ ssa_num n
    | Gen (v1, v2, n, _, _) -> NameGen.to_string () (mk_id (sprintf "%d.%d" v1 v2)) ^ ssa_num n
    | Name (id, n) when Config.register_file && IdSet.mem id !register_file_member_ids ->
        if !current_function_threaded then register_file_param ^ "->" ^ NameGen.to_string () id ^ ssa_num n
        else register_file_variable ^ "." ^ NameGen.to_string () id ^ ssa_num n
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

  (* The register's plain C symbol, without the register-file member prefix:
     used for the struct field names and the compatibility macros themselves. *)
  let sgen_register_file_symbol = function
    | Name (id, _) -> NameGen.to_string () id
    | reg -> c_error ("register " ^ string_of_name reg ^ " cannot be a model register file member")

  let codegen_id id = string (sgen_id id)

  let disambiguate_optimized_function_name str =
    if Config.optimized_model && Config.no_mangle && List.mem str ["u128"; "u256"; "u320"] then "as_" ^ str else str

  let sgen_function_id id =
    let str = NameGen.to_string () id |> disambiguate_optimized_function_name in
    if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)

  let sgen_function_uid uid =
    let str = sgen_uid uid |> disambiguate_optimized_function_name in
    if Config.no_mangle then str else !opt_prefix ^ String.sub str 1 (String.length str - 1)

  let codegen_function_id id = string (sgen_function_id id)

  let readable_ctyp_names = ref CTMap.empty
  let readable_ctyp_names_used = ref Util.StringSet.empty

  let fixed_bytes_type_name ctyp =
    let length = Option.get (c_repr_fixed_bytes_length ctyp) in
    match List.assoc_opt length Config.c_repr_fixed_bytes_names with
    | Some name -> name
    | None when is_c_repr_fixed_bytes_u64_lanes ctyp -> "fixed_bytes_u64_lanes_" ^ string_of_int length
    | None -> "fixed_bytes_" ^ string_of_int length

  let external_type_name = function CT_struct (id, []) -> Bindings.find_opt id Config.external_type_names | _ -> None

  let rec readable_ctyp_stem = function
    | ctyp when Option.is_some (external_type_name ctyp) -> Option.get (external_type_name ctyp)
    | ctyp when is_c_repr_const_byte_pointer ctyp ->
        "const_byte_pointer_" ^ Option.get (c_repr_byte_pointer_adapter ctyp)
    | ctyp when is_c_repr_byte_pointer ctyp -> "byte_pointer_" ^ Option.get (c_repr_byte_pointer_adapter ctyp)
    | ctyp when is_c_repr_u320 ctyp -> "u320"
    | ctyp when is_c_repr_u256 ctyp -> "u256"
    | ctyp when is_c_repr_fixed_bytes ctyp -> fixed_bytes_type_name ctyp
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
    | ctyp when Option.is_some (external_type_name ctyp) -> Option.get (external_type_name ctyp)
    | ctyp when is_c_repr_const_byte_pointer ctyp -> "const uint8_t *"
    | ctyp when is_c_repr_byte_pointer ctyp -> "uint8_t *"
    | ctyp when is_c_repr_u128 ctyp -> "u128"
    | ctyp when is_c_repr_u256 ctyp -> "u256"
    | ctyp when is_c_repr_u320 ctyp -> "u320"
    | ctyp when is_c_repr_fixed_bytes ctyp -> fixed_bytes_type_name ctyp
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
    | ctyp when Option.is_some (external_type_name ctyp) -> Option.get (external_type_name ctyp)
    | ctyp when is_c_repr_const_byte_pointer ctyp ->
        "const_byte_pointer_" ^ Option.get (c_repr_byte_pointer_adapter ctyp)
    | ctyp when is_c_repr_byte_pointer ctyp -> "byte_pointer_" ^ Option.get (c_repr_byte_pointer_adapter ctyp)
    | ctyp when is_c_repr_u128 ctyp -> "u128"
    | ctyp when is_c_repr_u256 ctyp -> "u256"
    | ctyp when is_c_repr_u320 ctyp -> "u320"
    | ctyp when is_c_repr_fixed_bytes ctyp -> fixed_bytes_type_name ctyp
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

  (* Distinct bounded Sail integer types frequently share one concrete C
     carrier.  Once any semantic range check has been emitted, spelling a cast
     between identical carriers adds no conversion and obscures the generated
     expression. *)
  let same_c_storage_type left right = String.equal (sgen_ctyp left) (sgen_ctyp right)

  let sgen_mask n =
    if n = 0 then "UINT64_C(0)"
    else if n <= 64 then (
      let chars_F = String.make (n / 4) 'F' in
      let first = match n mod 4 with 0 -> "" | 1 -> "1" | 2 -> "3" | 3 -> "7" | _ -> assert false in
      "UINT64_C(0x" ^ first ^ chars_F ^ ")"
    )
    else failwith "Tried to create a mask literal for a vector greater than 64 bits."

  let sgen_bitlist bs =
    let padding = (4 - (List.length bs mod 4)) mod 4 in
    Sail2_values.show_bitlist (Util.list_init padding (fun _ -> Sail2_values.B0) @ bs)

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
    let limbs = chunks 64 padded |> List.rev |> List.map (fun limb -> "UINT64_C(" ^ sgen_bitlist limb ^ ")") in
    "(u256){{" ^ String.concat ", " limbs ^ "}}"

  let sgen_u128_int value =
    let mask = max_uint 64 in
    let lo = Big_int.bitwise_and value mask in
    let hi = Big_int.shift_right value 64 in
    "(u128){{UINT64_C(" ^ Big_int.to_string lo ^ "), UINT64_C(" ^ Big_int.to_string hi ^ ")}}"

  let sgen_u256_int value =
    let mask = max_uint 64 in
    let limb shift = Big_int.shift_right value shift |> fun value -> Big_int.bitwise_and value mask in
    "(u256){{UINT64_C("
    ^ Big_int.to_string (limb 0)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 64)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 128)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 192)
    ^ ")}}"

  let sgen_u320_int value =
    let mask = max_uint 64 in
    let limb shift = Big_int.shift_right value shift |> fun value -> Big_int.bitwise_and value mask in
    "(u320){{UINT64_C("
    ^ Big_int.to_string (limb 0)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 64)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 128)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 192)
    ^ "), UINT64_C("
    ^ Big_int.to_string (limb 256)
    ^ ")}}"

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
    | VL_bits bs -> "UINT64_C(" ^ sgen_bitlist bs ^ ")"
    | VL_int i -> (
        match ctyp with
        | ctyp when is_c_repr_u320 ctyp -> sgen_u320_int i
        | ctyp when is_c_repr_u256 ctyp -> sgen_u256_int i
        | ctyp when is_c_repr_u128 ctyp -> sgen_u128_int i
        | CT_fuint width when width <= 64 -> "UINT" ^ string_of_int width ^ "_C(" ^ Big_int.to_string i ^ ")"
        | CT_fint width when width > 64 -> sgen_i128_int i
        | CT_fint width when width < 64 -> "INT" ^ string_of_int width ^ "_C(" ^ Big_int.to_string i ^ ")"
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
    | V_struct (fields, ctyp) ->
        sprintf "((%s){%s})" (sgen_ctyp ctyp)
          (Util.string_of_list ", "
             (fun (field, cval) -> "." ^ sgen_id field ^ " = " ^ sgen_cval_in_value_context cval)
             fields
          )
    | V_ctor_unwrap (f, ctor, _) -> sprintf "%s.variants.%s" (sgen_cval f) (sgen_uid ctor)
    | V_tuple values as tuple ->
        sprintf "((%s){%s})"
          (sgen_ctyp (cval_ctyp tuple))
          (Util.string_of_list ", "
             (fun (index, value) -> "." ^ sgen_tuple_id index ^ " = " ^ sgen_cval_in_value_context value)
             (List.mapi (fun index value -> (index, value)) values)
          )

  (* C's logical, comparison, and negation operators have type [int], even
     when both operands are [_Bool].  JIB correctly records their semantic
     result as [CT_bool], so make that representation boundary explicit only
     when the rendered expression is one of those native C operators.  Calls
     to generated equality/order helpers already return [bool] and must remain
     uncast: besides being clearer, this avoids redundant-cast diagnostics.

     Native operator expressions are parenthesized by [sgen_call], except for
     the deliberately compact [!flag] form.  Constructor-kind tests are the
     one comparison form emitted without outer parentheses. *)
  and sgen_cval_in_value_context cval =
    let rendered = sgen_cval cval in
    if ctyp_equal (cval_ctyp cval) CT_bool then (
      match cval with
      | V_ctor_kind _ -> sprintf "(bool)(%s)" rendered
      | V_call _ when String.length rendered > 0 && (rendered.[0] = '(' || rendered.[0] = '!') ->
          let rendered =
            let length = String.length rendered in
            if length >= 2 && rendered.[0] = '(' && rendered.[length - 1] = ')' then String.sub rendered 1 (length - 2)
            else rendered
          in
          sprintf "(bool)(%s)" rendered
      | _ -> rendered
    )
    else rendered

  and sgen_cval_as target_ctyp cval =
    let storage_width = function
      | CT_fuint width | CT_fint width -> Some (if width > 64 then 128 else native_c_integer_width width)
      | _ -> None
    in
    let widened_proven_binop operator left right =
      match (storage_width target_ctyp, storage_width (cval_ctyp cval)) with
      | Some target_width, Some source_width when target_width > source_width ->
          Some (sprintf "(%s %s %s)" (sgen_cval_as target_ctyp left) operator (sgen_cval_as target_ctyp right))
      | _ -> None
    in
    if same_c_storage_type target_ctyp (cval_ctyp cval) then sgen_cval cval
    else (
      match cval with
      | V_call (Proven_iadd, [left; right]) -> (
          match widened_proven_binop "+" left right with
          | Some expression -> expression
          | None -> sprintf "(%s)%s" (sgen_ctyp target_ctyp) (sgen_cval cval)
        )
      | V_call (Proven_isub, [left; right]) -> (
          match widened_proven_binop "-" left right with
          | Some expression -> expression
          | None -> sprintf "(%s)%s" (sgen_ctyp target_ctyp) (sgen_cval cval)
        )
      | V_call (Proven_imul, [left; right]) -> (
          match widened_proven_binop "*" left right with
          | Some expression -> expression
          | None -> sprintf "(%s)%s" (sgen_ctyp target_ctyp) (sgen_cval cval)
        )
      | _ -> sprintf "(%s)%s" (sgen_ctyp target_ctyp) (sgen_cval cval)
    )

  and sgen_proven_native_binop operator v1 v2 =
    let raw () = sprintf "(%s %s %s)" (sgen_cval v1) operator (sgen_cval v2) in
    match cval_ctyp v1 with
    | CT_fuint width when width < 32 ->
        sprintf "((%s)(%s %s %s))" (sgen_ctyp (CT_fuint width)) (sgen_cval_as (CT_fuint 32) v1) operator
          (sgen_cval_as (CT_fuint 32) v2)
    | CT_fint width when width < 32 ->
        sprintf "((%s)(%s %s %s))" (sgen_ctyp (CT_fint width)) (sgen_cval_as (CT_fint 32) v1) operator
          (sgen_cval_as (CT_fint 32) v2)
    | CT_fint _ | CT_fuint _ -> raw ()
    | ctyp when is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp ->
        (* A semantic proof can be attached while an integer still has a
           scalar JIB carrier and survive a later def/call-graph
           specialization to a plain wide-value carrier.  The proof remains
           valid, but C operators do not apply to those structs; use the same
           allocation-free helpers as ordinary wide arithmetic. *)
        let op =
          match operator with "+" -> Iadd | "-" -> Isub | "*" -> Imul | "/" -> Idiv | "%" -> Imod | _ -> assert false
        in
        sgen_call op [v1; v2]
    | _ ->
        failwith
          (Printf.sprintf "Proven native arithmetic requires fixed integer operands, got %s and %s"
             (string_of_ctyp (cval_ctyp v1))
             (string_of_ctyp (cval_ctyp v2))
          )

  and sgen_call op cvals =
    let macro_argument value =
      let rendered = sgen_cval value in
      match value with
      | V_lit (_, ctyp) when is_c_repr_u128 ctyp || is_c_repr_u256 ctyp || is_c_repr_u320 ctyp -> "(" ^ rendered ^ ")"
      | _ -> rendered
    in
    let u320_of value =
      match cval_ctyp value with
      | ctyp when is_c_repr_u320 ctyp -> sgen_cval value
      | ctyp when is_c_repr_u256 ctyp -> sprintf "u320_of_u256(%s)" (sgen_cval value)
      | ctyp when is_c_repr_u128 ctyp -> sprintf "u320_of_u128(%s)" (sgen_cval value)
      | CT_fuint _ -> sprintf "u320_of_u64(%s)" (sgen_cval value)
      | ctyp -> failwith ("Cannot widen " ^ string_of_ctyp ctyp ^ " to u320")
    in
    let native_ordering_operand value =
      match cval_ctyp value with CT_fuint width | CT_fint width -> width <= 64 | _ -> false
    in
    let native_ordering_pair left right = native_ordering_operand left && native_ordering_operand right in
    let mixed_native_comparison op left right =
      let compare_signed_unsigned signed_width unsigned_width signed unsigned =
        if signed_width > unsigned_width then None
        else (
          let signed = sgen_cval signed in
          let unsigned = sgen_cval unsigned in
          let zero = sgen_value (CT_fint signed_width) (VL_int Big_int.zero) in
          let converted = sprintf "((%s)%s)" (sgen_ctyp (CT_fuint unsigned_width)) signed in
          match op with
          | Eq -> Some (sprintf "(%s >= %s && %s == %s)" signed zero converted unsigned)
          | Neq -> Some (sprintf "(%s < %s || %s != %s)" signed zero converted unsigned)
          | Ilt -> Some (sprintf "(%s < %s || %s < %s)" signed zero converted unsigned)
          | Igt -> Some (sprintf "(%s > %s && %s > %s)" signed zero converted unsigned)
          | Ilteq -> Some (sprintf "(%s <= %s || %s <= %s)" signed zero converted unsigned)
          | Igteq -> Some (sprintf "(%s >= %s && %s >= %s)" signed zero converted unsigned)
          | _ -> None
        )
      in
      let compare_unsigned_signed unsigned_width signed_width unsigned signed =
        if signed_width > unsigned_width then None
        else (
          let unsigned = sgen_cval unsigned in
          let signed = sgen_cval signed in
          let zero = sgen_value (CT_fint signed_width) (VL_int Big_int.zero) in
          let converted = sprintf "((%s)%s)" (sgen_ctyp (CT_fuint unsigned_width)) signed in
          match op with
          | Eq -> Some (sprintf "(%s >= %s && %s == %s)" signed zero unsigned converted)
          | Neq -> Some (sprintf "(%s < %s || %s != %s)" signed zero unsigned converted)
          | Ilt -> Some (sprintf "(%s > %s && %s < %s)" signed zero unsigned converted)
          | Igt -> Some (sprintf "(%s < %s || %s > %s)" signed zero unsigned converted)
          | Ilteq -> Some (sprintf "(%s >= %s && %s <= %s)" signed zero unsigned converted)
          | Igteq -> Some (sprintf "(%s <= %s || %s >= %s)" signed zero unsigned converted)
          | _ -> None
        )
      in
      match (cval_ctyp left, cval_ctyp right) with
      | CT_fint signed_width, CT_fuint unsigned_width -> compare_signed_unsigned signed_width unsigned_width left right
      | CT_fuint unsigned_width, CT_fint signed_width -> compare_unsigned_signed unsigned_width signed_width left right
      | _ -> None
    in
    match (op, cvals) with
    | Bnot, [V_lit (VL_bool value, _)] -> if value then "false" else "true"
    | Bnot, [V_call (Bnot, [value])] -> sgen_cval value
    | Bnot, [V_call (Band, values)] -> sgen_call Bor (List.map (fun value -> V_call (Bnot, [value])) values)
    | Bnot, [V_call (Bor, values)] -> sgen_call Band (List.map (fun value -> V_call (Bnot, [value])) values)
    | Bnot, [V_call (Eq, [left; right])] -> sgen_call Neq [left; right]
    | Bnot, [V_call (Neq, [left; right])] -> sgen_call Eq [left; right]
    | Bnot, [V_call (Ilt, [left; right])] -> sgen_call Igteq [left; right]
    | Bnot, [V_call (Igt, [left; right])] -> sgen_call Ilteq [left; right]
    | Bnot, [V_call (Ilteq, [left; right])] -> sgen_call Igt [left; right]
    | Bnot, [V_call (Igteq, [left; right])] -> sgen_call Ilt [left; right]
    | Bnot, [((V_id _ | V_member _ | V_field _ | V_tuple_member _ | V_ctor_unwrap _) as v)] -> "!" ^ sgen_cval v
    | Bnot, [v] -> "!(" ^ sgen_cval v ^ ")"
    | Band, vs ->
        if List.exists (function V_lit (VL_bool false, _) -> true | _ -> false) vs then "false"
        else (
          let vs = List.filter (function V_lit (VL_bool true, _) -> false | _ -> true) vs in
          match vs with
          | [] -> "true"
          | [value] -> sgen_cval value
          | values -> "(" ^ Util.string_of_list " && " sgen_cval values ^ ")"
        )
    | Bor, vs ->
        if List.exists (function V_lit (VL_bool true, _) -> true | _ -> false) vs then "true"
        else (
          let vs = List.filter (function V_lit (VL_bool false, _) -> false | _ -> true) vs in
          match vs with
          | [] -> "false"
          | [value] -> sgen_cval value
          | values -> "(" ^ Util.string_of_list " || " sgen_cval values ^ ")"
        )
    | List_hd, [v] -> sprintf "(%s).hd" ("*" ^ sgen_cval v)
    | List_tl, [v] -> sprintf "(%s).tl" ("*" ^ sgen_cval v)
    | List_is_empty, [v] -> sprintf "(%s == NULL)" (sgen_cval v)
    | Eq, [v1; v2] -> (
        match mixed_native_comparison Eq v1 v2 with
        | Some comparison -> comparison
        | None -> (
            match (cval_ctyp v1, cval_ctyp v2) with
            | CT_unit, CT_unit when Config.optimized_model && !optimize_unit_results -> "true"
            | left, right when is_c_repr_byte_pointer left && ctyp_equal left right ->
                sprintf "(%s == %s)" (sgen_cval v1) (sgen_cval v2)
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
      )
    | Neq, [v1; v2] -> (
        match mixed_native_comparison Neq v1 v2 with
        | Some comparison -> comparison
        | None -> (
            match (cval_ctyp v1, cval_ctyp v2) with
            | CT_unit, CT_unit when Config.optimized_model && !optimize_unit_results -> "false"
            | left, right when is_c_repr_byte_pointer left && ctyp_equal left right ->
                sprintf "(%s != %s)" (sgen_cval v1) (sgen_cval v2)
            | CT_sbits _, _ -> sprintf "neq_sbits(%s, %s)" (sgen_cval v1) (sgen_cval v2)
            | left, right when is_c_repr_u320 left || is_c_repr_u320 right ->
                sprintf "(!eq_u320(%s, %s))" (u320_of v1) (u320_of v2)
            | left, right when is_c_repr_u256 left && is_c_repr_u128 right ->
                sprintf "(!u256_eq_u128(%s, %s))" (sgen_cval v1) (sgen_cval v2)
            | left, right when is_c_repr_u128 left && is_c_repr_u256 right ->
                sprintf "(!u256_eq_u128(%s, %s))" (sgen_cval v2) (sgen_cval v1)
            | left, CT_fuint _ when is_c_repr_u128 left -> sprintf "(!u128_eq_u64(%s, %s))" (sgen_cval v1) (sgen_cval v2)
            | CT_fuint _, right when is_c_repr_u128 right ->
                sprintf "(!u128_eq_u64(%s, %s))" (sgen_cval v2) (sgen_cval v1)
            | left, CT_fuint _ when is_c_repr_u256 left -> sprintf "(!u256_eq_u64(%s, %s))" (sgen_cval v1) (sgen_cval v2)
            | CT_fuint _, right when is_c_repr_u256 right ->
                sprintf "(!u256_eq_u64(%s, %s))" (sgen_cval v2) (sgen_cval v1)
            | ctyp, _ when is_c_repr_value ctyp ->
                sprintf "(!eq_%s(%s, %s))" (sgen_ctyp_name ctyp) (sgen_cval v1) (sgen_cval v2)
            | _ -> sprintf "(%s != %s)" (sgen_cval v1) (sgen_cval v2)
          )
      )
    | Ilt, [v1; v2] when Option.is_some (mixed_native_comparison Ilt v1 v2) ->
        Option.get (mixed_native_comparison Ilt v1 v2)
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
    | Igt, [v1; v2] when Option.is_some (mixed_native_comparison Igt v1 v2) ->
        Option.get (mixed_native_comparison Igt v1 v2)
    | Igt, [v1; v2] when native_ordering_pair v1 v2 -> sprintf "(%s > %s)" (sgen_cval v1) (sgen_cval v2)
    | Igt, [v1; v2] -> sgen_call Ilt [v2; v1]
    | Ilteq, [v1; v2] when Option.is_some (mixed_native_comparison Ilteq v1 v2) ->
        Option.get (mixed_native_comparison Ilteq v1 v2)
    | Ilteq, [v1; v2] when native_ordering_pair v1 v2 -> sprintf "(%s <= %s)" (sgen_cval v1) (sgen_cval v2)
    | Ilteq, [v1; v2] -> sprintf "(!%s)" (sgen_call Ilt [v2; v1])
    | Igteq, [v1; v2] when Option.is_some (mixed_native_comparison Igteq v1 v2) ->
        Option.get (mixed_native_comparison Igteq v1 v2)
    | Igteq, [v1; v2] when native_ordering_pair v1 v2 -> sprintf "(%s >= %s)" (sgen_cval v1) (sgen_cval v2)
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
    | Widening_iadd (320, _), [v1; v2] -> sprintf "u320_add_widen(%s, %s)" (macro_argument v1) (macro_argument v2)
    | Widening_imul (320, _), [v1; v2] -> sprintf "u320_mul_widen(%s, %s)" (macro_argument v1) (macro_argument v2)
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
        | left, (CT_fint _ | CT_fuint _ | CT_constant _) when is_c_repr_byte_pointer left ->
            sprintf "(%s + %s)" (sgen_cval v1) (sgen_cval v2)
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
        | ctyp -> c_error (sprintf "Cannot lower proved power-of-two division for %s" (string_of_ctyp ctyp))
      )
    | Power_of_two_imod exponent, [value] -> (
        match cval_ctyp value with
        | CT_fint _ | CT_fuint _ ->
            let mask = Big_int.pred (Big_int.pow_int_positive 2 exponent) in
            sprintf "(%s & %s)" (sgen_cval value) (sgen_cval (V_lit (VL_int mask, cval_ctyp value)))
        | ctyp -> c_error (sprintf "Cannot lower proved power-of-two remainder for %s" (string_of_ctyp ctyp))
      )
    | (Mixed_proven_idiv (operation_ctyp, result_ctyp) | Mixed_proven_imod (operation_ctyp, result_ctyp)), [left; right]
      ->
        ( match (operation_ctyp, cval_ctyp left, cval_ctyp right) with
        | (CT_fint _ | CT_fuint _), (CT_fint _ | CT_fuint _), (CT_fint _ | CT_fuint _) -> ()
        | operation_ctyp, left_ctyp, right_ctyp ->
            c_error
              (sprintf "Cannot lower mixed proved division with %s for %s and %s" (string_of_ctyp operation_ctyp)
                 (string_of_ctyp left_ctyp) (string_of_ctyp right_ctyp)
              )
        );
        let operator = match op with Mixed_proven_idiv _ -> "/" | _ -> "%" in
        let operation =
          sprintf "(%s %s %s)" (sgen_cval_as operation_ctyp left) operator (sgen_cval_as operation_ctyp right)
        in
        if same_c_storage_type result_ctyp operation_ctyp then operation
        else sprintf "((%s)%s)" (sgen_ctyp result_ctyp) operation
    | Unsigned width, [V_lit (VL_int value, _)] -> sgen_value (CT_fuint width) (VL_int value)
    | Unsigned width, [vec] -> sgen_cval_as (CT_fuint width) vec
    | Signed width, [value] -> (
        match cval_ctyp value with
        | CT_fbits n when width = 64 -> sprintf "fast_signed(%s, %d)" (sgen_cval value) n
        | CT_fint _ | CT_fuint _ | CT_constant _ -> sgen_cval_as (CT_fint width) value
        | ctyp -> c_error (sprintf "Cannot lower proved signed conversion from %s" (string_of_ctyp ctyp))
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
        | CT_fbits width -> sprintf "((%s << %s) & %s)" (sgen_cval value) (sgen_cval amount) (sgen_mask width)
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
            sprintf "((%s >> %s) | (%s ? (%s ^ (%s >> %s)) : UINT64_C(0)))" (sgen_cval value) (sgen_cval amount) sign
              mask mask (sgen_cval amount)
        | _ -> assert false
      )
    | (Proven_bvshiftl _ | Proven_bvshiftr _ | Proven_bvarith_shiftr _), _ -> assert false
    | Bvrotr (width, amount), [value] when 0 < width && width <= 64 && 0 < amount && amount < width -> (
        match cval_ctyp value with
        | CT_fbits source_width when width <= source_width ->
            let masked = sprintf "(%s & %s)" (sgen_cval value) (sgen_mask width) in
            sprintf "(((%s >> %d) | (%s << %d)) & %s)" masked amount masked (width - amount) (sgen_mask width)
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
    | Proven_vector_access length, [vector; index] -> (
        match cval_ctyp vector with
        | CT_fvector (actual_length, _) when length = actual_length ->
            sprintf "%s.data[(size_t)%s]" (sgen_cval vector) (sgen_cval index)
        | _ -> assert false
      )
    | Slice len, [vec; start] -> (
        match cval_ctyp vec with
        | CT_fbits _ ->
            sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & safe_rshift(%s, %s))" len (sgen_cval vec) (sgen_cval start)
        | CT_fuint _ ->
            sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & safe_rshift(%s, %s))" len (sgen_cval vec) (sgen_cval start)
        | CT_sbits _ ->
            sprintf "(safe_rshift(UINT64_MAX, 64 - %d) & safe_rshift(%s.bits, %s))" len (sgen_cval vec) (sgen_cval start)
        | ctyp when is_c_repr_u128 ctyp ->
            let extracted = sprintf "u128_extract_u64(%s, (uint64_t)(%s))" (sgen_cval vec) (sgen_cval start) in
            if len = 64 then extracted else sprintf "(%s & %s)" (sgen_mask len) extracted
        | ctyp when is_c_repr_u256 ctyp ->
            let extracted = sprintf "u256_extract_u64(%s, (uint64_t)(%s))" (sgen_cval vec) (sgen_cval start) in
            if len = 64 then extracted else sprintf "(%s & %s)" (sgen_mask len) extracted
        | _ -> assert false
      )
    | Proven_slice (len, 64), [vec; start] ->
        let extracted =
          match cval_ctyp vec with
          | CT_fbits _ | CT_fuint _ -> sprintf "(%s >> %s)" (sgen_cval vec) (sgen_cval start)
          | CT_sbits _ -> sprintf "(%s.bits >> %s)" (sgen_cval vec) (sgen_cval start)
          | _ -> assert false
        in
        if len = 64 then extracted else sprintf "(%s & %s)" (sgen_mask len) extracted
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
    | CT_unit when Config.optimized_model && !optimize_unit_results -> string "true"
    | ctyp when is_c_repr_byte_pointer ctyp -> ksprintf string "(%s == %s)" arg1 arg2
    | CT_ref _ -> ksprintf string "(%s == %s)" arg1 arg2
    | CT_fint _ | CT_fuint _ -> ksprintf string "(%s == %s)" arg1 arg2
    | ctyp ->
        let helper = "eq_" ^ sgen_ctyp_name ctyp in
        current_static_helper_demands := Util.StringSet.add helper !current_static_helper_demands;
        ( match ctyp with
        | CT_struct _ | CT_variant _ | CT_enum _ | CT_tup _ | CT_list _ | CT_vector _ | CT_fvector _ ->
            if not (Util.StringSet.mem helper !static_equality_declaration_names) then (
              static_equality_declaration_names := Util.StringSet.add helper !static_equality_declaration_names;
              static_equality_declarations :=
                (helper, ksprintf string "static bool %s(%s op1, %s op2);" helper (sgen_ctyp ctyp) (sgen_ctyp ctyp))
                :: !static_equality_declarations
            )
        | _ -> ()
        );
        sail_equal (sgen_ctyp_name ctyp) "%s, %s" arg1 arg2

  (* Native C equality operators produce [int].  When an equality expression
     is itself the value returned by a generated [_Bool] helper, make that
     representation conversion explicit.  Equality helper calls already
     return [bool], so retaining them verbatim avoids redundant casts. *)
  let codegen_equal_in_bool_value ctyp arg1 arg2 =
    let equality = codegen_equal ctyp arg1 arg2 in
    match ctyp with
    | ctyp when is_c_repr_byte_pointer ctyp -> string "(bool)" ^^ equality
    | CT_ref _ | CT_fint _ | CT_fuint _ -> string "(bool)" ^^ equality
    | _ -> equality

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
      let value = sgen_cval_as ctyp_to cval in
      ksprintf string "  %s = %s;" (sgen_clexp_pure l clexp) value
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
    let fits_unsigned width = integer_cval_fits Big_int.zero (max_uint width) cval in
    let fits_signed width = integer_cval_fits (min_int width) (max_int width) cval in
    match (ctyp_to, ctyp_from) with
    | CT_fuint to_width, CT_fuint from_width ->
        let to_width = storage_width to_width in
        let from_width = storage_width from_width in
        if from_width <= to_width || fits_unsigned to_width then assignment
        else
          checked (sprintf "%s > %s" (sgen_cval cval) (upper_unsigned_bound ctyp_to to_width)) (outside_target_domain ())
          ^^ assignment
    | CT_fint to_width, CT_fint from_width ->
        let to_width = storage_width to_width in
        let from_width = storage_width from_width in
        if from_width <= to_width || fits_signed to_width then assignment
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
        if fits_unsigned to_width then assignment
        else if from_width <= to_width then negative ^^ assignment
        else
          negative
          ^^ checked
               (sprintf "%s > %s" (sgen_cval cval) (upper_unsigned_bound ctyp_to to_width))
               (outside_target_domain ())
          ^^ assignment
    | CT_fint to_width, CT_fuint from_width ->
        let to_width = storage_width to_width in
        let from_width = storage_width from_width in
        if from_width < to_width || fits_signed to_width then assignment
        else
          checked (sprintf "%s > %s" (sgen_cval cval) (upper_signed_bound ctyp_to to_width)) (outside_target_domain ())
          ^^ assignment
    | _ -> assert false

  (* Return the expression for conversions that can be written directly in a
     stack-local initializer.  Checked native-integer conversions deliberately
     return [None]: their guard must execute before the assignment, so keeping
     a separate declaration is the honest C representation. *)
  let stack_conversion_initializer ctyp_to cval =
    let ctyp_from = cval_ctyp cval in
    let value = if ctyp_equal ctyp_to ctyp_from then sgen_cval_in_value_context cval else sgen_cval cval in
    let call helper = Some (sprintf "%s(%s)" helper value) in
    let cast_call helper =
      let call = sprintf "%s(%s)" helper value in
      if String.equal (sgen_ctyp ctyp_to) "uint64_t" then Some call else Some (sprintf "(%s)%s" (sgen_ctyp ctyp_to) call)
    in
    let cast () = Some (sgen_cval_as ctyp_to cval) in
    let storage_width width = if width > 64 then 128 else native_c_integer_width width in
    if ctyp_equal ctyp_to ctyp_from then Some value
    else (
      match (ctyp_to, ctyp_from) with
      | to_typ, (CT_fint _ | CT_fuint _ | CT_constant _) when is_c_repr_byte_pointer to_typ ->
          let adapter = Option.get (c_repr_byte_pointer_adapter to_typ) in
          if adapter = direct_byte_pointer_adapter then (
            match cval with
            | V_lit (VL_int literal, _) when Big_int.equal literal Big_int.zero -> Some "NULL"
            | _ -> None
          )
          else Some (sprintf "%s((uint64_t)%s)" adapter value)
      | CT_fuint to_width, CT_fuint from_width when storage_width from_width <= storage_width to_width -> cast ()
      | CT_fuint to_width, (CT_fuint _ | CT_fint _ | CT_constant _)
        when integer_cval_fits Big_int.zero (max_uint (storage_width to_width)) cval ->
          cast ()
      | CT_fint to_width, CT_fint from_width when storage_width from_width <= storage_width to_width -> cast ()
      | CT_fint to_width, (CT_fuint _ | CT_fint _ | CT_constant _)
        when integer_cval_fits (min_int (storage_width to_width)) (max_int (storage_width to_width)) cval ->
          cast ()
      | CT_fint to_width, CT_fuint from_width when storage_width from_width < storage_width to_width -> cast ()
      | to_typ, CT_fuint _ when is_c_repr_u320 to_typ -> call "u320_of_u64"
      | to_typ, from_typ when is_c_repr_u320 to_typ && is_c_repr_u128 from_typ -> call "u320_of_u128"
      | to_typ, from_typ when is_c_repr_u320 to_typ && is_c_repr_u256 from_typ -> call "u320_of_u256"
      | (CT_fint _ | CT_fuint _), from_typ when is_c_repr_u320 from_typ -> cast_call "u320_to_u64"
      | to_typ, from_typ when is_c_repr_u256 to_typ && is_c_repr_u320 from_typ -> call "u256_of_u320"
      | to_typ, from_typ when is_c_repr_u128 to_typ && is_c_repr_u320 from_typ -> call "u128_of_u320"
      | to_typ, CT_fbits _ when is_c_repr_u256 to_typ -> call "u256_of_fbits"
      | to_typ, CT_fuint _ when is_c_repr_u256 to_typ -> call "u256_of_fbits"
      | to_typ, from_typ when is_c_repr_u256 to_typ && is_c_repr_u128 from_typ -> call "u256_of_u128"
      | (CT_fint _ | CT_fuint _), from_typ when is_c_repr_u256 from_typ -> cast_call "u256_to_u64"
      | to_typ, CT_fuint _ when is_c_repr_u128 to_typ -> call "u128_of_u64"
      | to_typ, CT_fint width when is_c_repr_u128 to_typ && width > 64 ->
          Some (sprintf "(u128){{(uint64_t)%s, (uint64_t)(((unsigned __int128)%s) >> 64)}}" value value)
      | (CT_fint _ | CT_fuint _), from_typ when is_c_repr_u128 from_typ -> cast_call "u128_to_u64"
      | to_typ, from_typ when is_c_repr_u128 to_typ && is_c_repr_u256 from_typ -> call "u128_of_u256"
      | _ -> None
    )

  (* A semantic byte vector becomes a fixed C byte aggregate through a small
     fill loop.  Keep initialization configurable so an adjacent declaration
     can initialize the aggregate on that same line and then emit only the
     loop.  Besides producing idiomatic C, the explicit zero value makes the
     conversion visibly total to Clang's dataflow analysis. *)
  let codegen_fixed_bytes_vector_conversion l clexp cval to_typ ~initialize =
    let length = Option.get (c_repr_fixed_bytes_length to_typ) in
    let i = ngensym () in
    let initialization =
      if initialize then
        ksprintf string "  %s = %s_zero();" (sgen_clexp_pure l clexp) (sgen_ctyp_name to_typ) ^^ hardline
      else empty
    in
    let update =
      if is_c_repr_fixed_bytes_u64_lanes to_typ then
        ksprintf string "    %s = fast_unsigned_vector_update_%s(%s, %s, %s.data[%s]);" (sgen_clexp_pure l clexp)
          (sgen_ctyp_name to_typ) (sgen_clexp_pure l clexp) (sgen_name i) (sgen_cval cval) (sgen_name i)
      else
        ksprintf string "    %s.bytes[%s] = (uint8_t)(%s.data[%s] & UINT64_C(0xff));" (sgen_clexp_pure l clexp)
          (sgen_name i) (sgen_cval cval) (sgen_name i)
    in
    initialization
    ^^ ksprintf string "  for (size_t %s = 0; %s < %d; ++%s) {" (sgen_name i) (sgen_name i) length (sgen_name i)
    ^^ hardline ^^ update ^^ hardline ^^ string "  }"

  (** Generate instructions to copy from a cval to a clexp. This will insert any needed type conversions from big
      integers to small integers (or vice versa), or from arbitrary-length bitvectors to and from uint64 bitvectors as
      needed. *)
  let rec codegen_conversion l ctx clexp cval =
    let ctyp_to = clexp_ctyp clexp in
    let ctyp_from = cval_ctyp cval in
    let assign_u64_call helper =
      let call = sprintf "%s(%s)" helper (sgen_cval cval) in
      let value =
        if String.equal (sgen_ctyp ctyp_to) "uint64_t" then call else sprintf "(%s)%s" (sgen_ctyp ctyp_to) call
      in
      ksprintf string "  %s = %s;" (sgen_clexp_pure l clexp) value
    in
    match (ctyp_to, ctyp_from) with
    (* When both types are equal, we don't need any conversion. *)
    | _, _ when ctyp_equal ctyp_to ctyp_from ->
        if is_stack_ctyp ctx ctyp_to then
          ksprintf string "  %s = %s;" (sgen_clexp_pure l clexp) (sgen_cval_in_value_context cval)
        else
          sail_copy ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) "%s, %s" (sgen_clexp l clexp)
            (sgen_cval_in_value_context cval)
    | to_typ, (CT_fint _ | CT_fuint _ | CT_constant _) when is_c_repr_byte_pointer to_typ ->
        let adapter = Option.get (c_repr_byte_pointer_adapter to_typ) in
        if adapter = direct_byte_pointer_adapter then (
          match cval with
          | V_lit (VL_int value, _) when Big_int.equal value Big_int.zero ->
              ksprintf string "  %s = NULL;" (sgen_clexp_pure l clexp)
          | _ ->
              raise
                (Reporting.err_general l
                   "C backend: an adapter-free $[c_repr byte_pointer] value cannot be constructed from a semantic \
                    integer other than literal zero"
                )
        )
        else ksprintf string "  %s = %s((uint64_t)%s);" (sgen_clexp_pure l clexp) adapter (sgen_cval cval)
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
    | (CT_fint _ | CT_fuint _), from_typ when is_c_repr_u320 from_typ -> assign_u64_call "u320_to_u64"
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
    | (CT_fint _ | CT_fuint _), from_typ when is_c_repr_u256 from_typ -> assign_u64_call "u256_to_u64"
    | to_typ, CT_fuint _ when is_c_repr_u128 to_typ ->
        ksprintf string "  %s = u128_of_u64(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, CT_fint width when is_c_repr_u128 to_typ && width > 64 ->
        ksprintf string "  %s = (u128){{(uint64_t)%s, (uint64_t)(((unsigned __int128)%s) >> 64)}};"
          (sgen_clexp_pure l clexp) (sgen_cval cval) (sgen_cval cval)
    | to_typ, CT_lint when is_c_repr_u128 to_typ ->
        ksprintf string "  %s = u128_of_sail_int(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | (CT_fint _ | CT_fuint _), from_typ when is_c_repr_u128 from_typ -> assign_u64_call "u128_to_u64"
    | to_typ, from_typ when is_c_repr_u128 to_typ && is_c_repr_u256 from_typ ->
        ksprintf string "  %s = u128_of_u256(%s);" (sgen_clexp_pure l clexp) (sgen_cval cval)
    | to_typ, (CT_vector (CT_fbits 8 | CT_fuint 8) | CT_fvector (_, (CT_fbits 8 | CT_fuint 8)))
      when is_c_repr_fixed_bytes to_typ ->
        codegen_fixed_bytes_vector_conversion l clexp cval to_typ ~initialize:true
    | (CT_vector (CT_fbits 8 | CT_fuint 8) | CT_fvector (_, (CT_fbits 8 | CT_fuint 8))), from_typ
      when is_c_repr_fixed_bytes from_typ ->
        let length = Option.get (c_repr_fixed_bytes_length from_typ) in
        let i = ngensym () in
        sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp_to) "%s" (sgen_clexp l clexp)
        ^^ hardline
        ^^ ksprintf string "  internal_vector_init_%s(%s, INT64_C(%d));" (sgen_ctyp_name ctyp_to) (sgen_clexp l clexp)
             length
        ^^ hardline
        ^^ ksprintf string "  for (size_t %s = 0; %s < %d; ++%s) {" (sgen_name i) (sgen_name i) length (sgen_name i)
        ^^ hardline
        ^^ ( if is_c_repr_fixed_bytes_u64_lanes from_typ then
               ksprintf string "    %s.data[%s] = fast_unsigned_vector_access_%s(%s, %s);" (sgen_clexp_pure l clexp)
                 (sgen_name i) (sgen_ctyp_name from_typ) (sgen_cval cval) (sgen_name i)
             else
               ksprintf string "    %s.data[%s] = (uint64_t)%s.bytes[%s];" (sgen_clexp_pure l clexp) (sgen_name i)
                 (sgen_cval cval) (sgen_name i)
           )
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

  let erase_unit_values = Config.optimized_model && !optimize_unit_results

  let retain_c_parameter ctyp = not (erase_unit_values && ctyp_equal ctyp CT_unit)

  let c_parameter_items parameters =
    let parameters = List.filter (fun (ctyp, _) -> retain_c_parameter ctyp) parameters in
    List.map (fun (ctyp, name) -> sgen_const_ctyp ctyp ^ if String.equal name "" then "" else " " ^ name) parameters

  let c_parameter_list ?(thread_regs = false) parameters =
    let parameters = c_parameter_items parameters in
    let parameters = if thread_regs then register_file_thread_parameter :: parameters else parameters in
    match (erase_unit_values, !opt_extra_params, parameters) with
    | true, None, [] -> "void"
    | _ -> extra_params () ^ String.concat ", " parameters

  (* An adjacent stack-local declaration and returning call can be emitted as
     one ordinary C initializer.  Keep this code-generation-only: JIB still
     models calls explicitly, which is important to the effect and exception
     passes, while the final optimized C need not expose that administrative
     split. *)
  let stack_call_initializer = ref None

  let stack_call_initializer_compatible declared destination =
    ctyp_equal declared destination
    ||
    let native_integer = function
      | CT_fuint width | CT_fint width -> width <= 64
      | CT_fbits width -> width <= 64
      | _ -> false
    in
    native_integer declared && native_integer destination

  let sgen_stack_call_destination l ctyp clexp =
    match (!stack_call_initializer, clexp) with
    | Some (declared, declared_ctyp), CL_id (destination, destination_ctyp)
      when Name.compare declared destination = 0
           && stack_call_initializer_compatible declared_ctyp ctyp
           && stack_call_initializer_compatible declared_ctyp destination_ctyp ->
        sprintf "%s %s" (sgen_ctyp declared_ctyp) (sgen_name declared)
    | _ -> sgen_clexp_pure l clexp

  (* [sgen_cval] parenthesizes C operators so that values remain safe when
     embedded in larger expressions.  A control-flow condition supplies its
     own mandatory parentheses, however, and emitting both layers produces
     the conspicuous [if ((a < b))] form.  Remove exactly one pair only when
     it encloses the complete rendered expression; nested casts and grouping
     inside the expression are left intact. *)
  let sgen_condition cval =
    let rendered = sgen_cval cval in
    let length = String.length rendered in
    let outer_parentheses_enclose_all () =
      if length < 2 || rendered.[0] <> '(' || rendered.[length - 1] <> ')' then false
      else (
        let rec scan index depth =
          if index = length then depth = 0
          else (
            let depth = match rendered.[index] with '(' -> depth + 1 | ')' -> depth - 1 | _ -> depth in
            depth >= 0 && (index = length - 1 || depth > 0) && scan (index + 1) depth
          )
        in
        scan 0 0
      )
    in
    if outer_parentheses_enclose_all () then String.sub rendered 1 (length - 2) else rendered

  (* JIB lowers source matches to failure branches before C emission. Recover a
     switch only when every branch excludes constructors or enum members from
     the same pure selector. Guarded and heterogeneous matches deliberately do
     not fit this shape and remain ordinary if statements. *)
  let switch_family_labels ctx selector =
    match cval_ctyp selector with
    | CT_variant (id, _) -> (
        match Bindings.find_opt id ctx.variants with
        | Some (_, constructors) ->
            Some (Bindings.bindings constructors |> List.map (fun (constructor, _) -> "Kind_" ^ sgen_id constructor))
        | None -> None
      )
    | CT_enum id ->
        Option.map (fun members -> IdSet.elements members |> List.map sgen_id) (Bindings.find_opt id ctx.enums)
    (* Literal ladders over a byte-bounded unsigned selector form a closed
       family of at most 256 dense tags.  This recognition exists to feed the
       constant-arm table lowering, so it stays behind the same flag. *)
    | CT_fuint width when Config.const_match_tables && width <= 8 -> Some (List.init (1 lsl width) string_of_int)
    | _ -> None

  let literal_switch_label selector literal =
    match cval_ctyp selector with
    | CT_fuint width
      when Config.const_match_tables && width <= 8 && Big_int.less_equal Big_int.zero literal
           && Big_int.less literal (Big_int.pow_int_positive 2 width) ->
        Some (Big_int.to_string literal)
    | _ -> None

  let rec switch_failure_cases ctx = function
    | V_ctor_kind (selector, ctor) ->
        Option.map
          (fun family -> (sgen_cval selector ^ ".kind", family, ["Kind_" ^ sgen_uid ctor]))
          (switch_family_labels ctx selector)
    | V_call (Neq, [V_member (member, _); selector]) ->
        Option.map (fun family -> (sgen_cval selector, family, [sgen_id member])) (switch_family_labels ctx selector)
    | V_call (Neq, [selector; V_member (member, _)]) ->
        Option.map (fun family -> (sgen_cval selector, family, [sgen_id member])) (switch_family_labels ctx selector)
    | V_call (Neq, [V_lit (VL_int literal, _); (V_id _ as selector)])
    | V_call (Neq, [(V_id _ as selector); V_lit (VL_int literal, _)]) -> (
        match literal_switch_label selector literal with
        | Some label ->
            Option.map (fun family -> (sgen_cval selector, family, [label])) (switch_family_labels ctx selector)
        | None -> None
      )
    | V_call (Band, [left; right]) -> (
        match (switch_failure_cases ctx left, switch_failure_cases ctx right) with
        | Some (left_selector, left_family, left_cases), Some (right_selector, right_family, right_cases)
          when String.equal left_selector right_selector && left_family = right_family ->
            Some (left_selector, left_family, left_cases @ right_cases)
        | _ -> None
      )
    | _ -> None

  let rec collect_switch_cases ctx expected_selector expected_family cases instr =
    match instr with
    | I_if (condition, then_instrs, (_ :: _ as case_body)) -> (
        match switch_failure_cases ctx condition with
        | Some (selector, family, labels)
          when Option.fold ~none:true ~some:(String.equal selector) expected_selector
               && Option.fold ~none:true ~some:(( = ) family) expected_family -> (
            let cases = cases @ [(labels, case_body)] in
            match then_instrs with
            | [I_aux (next, _)] -> (
                match collect_switch_cases ctx (Some selector) (Some family) cases next with
                | Some result -> Some result
                | None -> Some (selector, family, cases, then_instrs)
              )
            | default_body -> Some (selector, family, cases, default_body)
          )
        | _ -> None
      )
    | I_block [I_aux (instr, _)] -> collect_switch_cases ctx expected_selector expected_family cases instr
    | _ -> None

  let rec switch_branch_exits ctx = function
    | [] -> false
    | instr :: rest ->
        let exits_here =
          match instr with
          | instr when is_noreturn_call ctx instr -> true
          | I_aux ((I_return _ | I_goto _ | I_exit _ | I_throw _ | I_undefined _), _) -> true
          | I_aux (I_funcall (CR_one (CL_id (Return _, _)), _, _, _), _) -> true
          | I_aux (I_if (_, then_instrs, else_instrs), _) when else_instrs <> [] ->
              switch_branch_exits ctx then_instrs && switch_branch_exits ctx else_instrs
          | I_aux ((I_block instrs | I_try_block instrs), _) -> switch_branch_exits ctx instrs
          | _ -> false
        in
        exits_here || switch_branch_exits ctx rest

  (* Terminal-return sinking turns a match ladder into a sequence of guards:
       if (tag != A) { ...remaining cases... }
       return body_for_A;
     Recover the same switch shape from that equivalent form as well.  The
     exit requirement prevents absorbing statements that belong after a
     non-terminal match. *)
  let rec collect_terminal_switch_cases ctx allow_fallthrough_case expected_selector expected_family cases = function
    | I_aux (I_if (condition, then_instrs, []), _) :: (_ :: _ as case_body)
      when switch_branch_exits ctx case_body || (allow_fallthrough_case && cases = []) -> (
        match switch_failure_cases ctx condition with
        | Some (selector, family, labels)
          when Option.fold ~none:true ~some:(String.equal selector) expected_selector
               && Option.fold ~none:true ~some:(( = ) family) expected_family -> (
            let cases = cases @ [(labels, case_body)] in
            match collect_terminal_switch_cases ctx false (Some selector) (Some family) cases then_instrs with
            | Some result -> Some result
            | None when switch_branch_exits ctx then_instrs -> Some (selector, family, cases, then_instrs)
            | None -> None
          )
        | _ -> None
      )
    | [I_aux (I_block instrs, _)] ->
        collect_terminal_switch_cases ctx allow_fallthrough_case expected_selector expected_family cases instrs
    | _ -> None

  (* Return a C conditional expression only for the exact JIB shape produced
     by a value-valued Sail [if]: both arms copy pure values to one destination.
     Reusing [stack_conversion_initializer] is intentionally conservative: it
     excludes conversions whose checks or representation copies must remain
     statements, and therefore preserves branch-selective evaluation. *)
  let conditional_assignment_expression ctx condition then_destination then_value else_destination else_value =
    let destination_ctyp = clexp_ctyp then_destination in
    if
      Config.optimized_model && (not Config.cpp)
      && Stdlib.compare then_destination else_destination = 0
      && is_stack_ctyp ctx destination_ctyp
    then (
      match
        ( stack_conversion_initializer destination_ctyp then_value,
          stack_conversion_initializer destination_ctyp else_value
        )
      with
      | Some then_expression, Some else_expression -> (
          let condition_expression = sgen_condition condition in
          match condition with
          | V_lit (VL_bool true, CT_bool) -> Some then_expression
          | V_lit (VL_bool false, CT_bool) -> Some else_expression
          | _ when ctyp_equal destination_ctyp CT_bool ->
              let render_bool value = sgen_cval_in_value_context value in
              let expression =
                match (then_expression, else_expression) with
                | "true", "false" -> render_bool condition
                | "false", "true" -> render_bool (V_call (Bnot, [condition]))
                | "true", _ -> render_bool (V_call (Bor, [condition; else_value]))
                | "false", _ -> render_bool (V_call (Band, [V_call (Bnot, [condition]); else_value]))
                | _, "true" -> render_bool (V_call (Bor, [V_call (Bnot, [condition]); then_value]))
                | _, "false" -> render_bool (V_call (Band, [condition; then_value]))
                | _ -> sprintf "%s ? %s : %s" condition_expression then_expression else_expression
              in
              Some expression
          | _ -> Some (sprintf "%s ? %s : %s" condition_expression then_expression else_expression)
        )
      | _ -> None
    )
    else None

  (* --c-const-match-tables: a recovered switch arm is "constant" when its
     body is exactly one return (or one copy) of a value composed entirely of
     literals and enum members.  Enough such arms lower to a [static const]
     table indexed by the dense selector tag; payload-reading arms stay in a
     residual switch whose default reads the table.  Classification runs on
     the collected arms BEFORE identical-body merging, and the exact-shape
     requirement rejects any arm carrying additional instructions (including
     coverage instrumentation calls). *)

  type constant_arm_exit = Constant_arm_return | Constant_arm_copy of Parse_ast.l * clexp * string option

  type constant_switch_table = {
    table_declaration : document;
    (* Statement lines for the table read; [in_switch] selects the trailing
       break when the residual switch survives around them. *)
    table_read : in_switch:bool -> string list;
    table_read_declares : bool;
    residual_cases : (string list * instr list) list;
  }

  let constant_arm_exits_agree first second =
    match (first, second) with
    | Constant_arm_return, Constant_arm_return -> true
    | Constant_arm_copy (_, first_destination, first_label), Constant_arm_copy (_, second_destination, second_label) ->
        Stdlib.compare first_destination second_destination = 0 && first_label = second_label
    | _ -> false

  let rec constant_table_value = function
    | V_lit ((VL_int _ | VL_bool _ | VL_bits _ | VL_enum _), _) -> true
    | V_member _ -> true
    (* Proved representation conversions of literals render as literal
       constants ([integer_literal_value] recurses only through them). *)
    | V_call ((Unsigned _ | Zero_extend _), [_]) as conversion -> Option.is_some (integer_literal_value conversion)
    | V_struct (fields, _) -> List.for_all (fun (_, field_value) -> constant_table_value field_value) fields
    | V_tuple members -> List.for_all constant_table_value members
    | _ -> false

  let classify_constant_arm body =
    match List.filter (function I_aux (I_comment _, _) -> false | _ -> true) body with
    | [I_aux (I_return value, _)] when constant_table_value value -> Some (Constant_arm_return, value)
    | [I_aux (I_copy (destination, value), (_, l))] when constant_table_value value ->
        Some (Constant_arm_copy (l, destination, None), value)
    | [I_aux (I_copy (destination, value), (_, l)); I_aux (I_goto label, _)] when constant_table_value value ->
        Some (Constant_arm_copy (l, destination, Some label), value)
    | _ -> None

  let constant_table_members = function
    | V_struct (fields, _) -> Some (List.map (fun (field, field_value) -> (sgen_id field, field_value)) fields)
    | V_tuple members -> Some (List.mapi (fun index member -> (sgen_tuple_id index, member)) members)
    | _ -> None

  (* Aggregates of nonnegative fixed unsigned literals pack into one integer
     per table entry, first member in the most significant lanes at its native
     storage width.  Everything else keeps its aggregate initializer. *)
  let packed_constant_layout values =
    let layout_of value =
      match constant_table_members value with
      | Some members ->
          List.fold_right
            (fun (member_name, member_value) layout ->
              match (layout, cval_ctyp member_value, integer_literal_value member_value) with
              | Some fields, CT_fuint width, Some literal when width <= 64 && Big_int.less_equal Big_int.zero literal ->
                  Some ((member_name, native_c_integer_width width, CT_fuint width) :: fields)
              | _ -> None
            )
            members (Some [])
      | None -> None
    in
    match values with
    | [] -> None
    | first :: rest -> (
        match layout_of first with
        | Some (_ :: _ as layout) when List.fold_left (fun total (_, width, _) -> total + width) 0 layout <= 64 ->
            let same_layout value =
              match layout_of value with
              | Some other ->
                  List.length other = List.length layout
                  && List.for_all2
                       (fun (name, width, _) (other_name, other_width, _) ->
                         String.equal name other_name && width = other_width
                       )
                       layout other
              | None -> false
            in
            if List.for_all same_layout rest then Some layout else None
        | _ -> None
      )

  let packed_constant_entry layout value =
    let members = Option.get (constant_table_members value) in
    List.fold_left
      (fun entry (member_name, width, _) ->
        let literal = Option.get (integer_literal_value (List.assoc member_name members)) in
        Big_int.add (Big_int.mul entry (Big_int.pow_int_positive 2 width)) literal
      )
      Big_int.zero layout

  let packed_constant_unpack result_ctyp layout entry_expression =
    let _, members =
      List.fold_right
        (fun (member_name, width, member_ctyp) (offset, rendered) ->
          let shifted = if offset = 0 then entry_expression else sprintf "(%s >> %d)" entry_expression offset in
          (offset + width, sprintf ".%s = (%s)%s" member_name (sgen_ctyp member_ctyp) shifted :: rendered)
        )
        layout (0, [])
    in
    sprintf "((%s){%s})" (sgen_ctyp result_ctyp) (String.concat ", " members)

  let rec sgen_constant_table_initializer value =
    match constant_table_members value with
    | Some members ->
        sprintf "{%s}"
          (Util.string_of_list ", "
             (fun (member_name, member_value) ->
               sprintf ".%s = %s" member_name (sgen_constant_table_initializer member_value)
             )
             members
          )
    | None -> sgen_cval_in_value_context value

  let constant_table_counter = ref 0

  let collected_switch_constant_table ctx selector cases =
    if (not Config.const_match_tables) || Config.cpp || Option.is_some Config.branch_coverage then None
    else (
      let classified = List.map (fun (labels, body) -> (labels, body, classify_constant_arm body)) cases in
      let constant_arms =
        List.filter_map (function labels, _, Some (exit, value) -> Some (labels, exit, value) | _ -> None) classified
      in
      let residual_cases =
        List.filter_map (function labels, body, None -> Some (labels, body) | _ -> None) classified
      in
      match constant_arms with
      | (_, first_exit, first_value) :: rest when List.length constant_arms >= 8 ->
          let result_ctyp = cval_ctyp first_value in
          if
            List.for_all
              (fun (_, exit, value) ->
                constant_arm_exits_agree first_exit exit && ctyp_equal (cval_ctyp value) result_ctyp
              )
              rest
            && is_stack_ctyp ctx result_ctyp
            && not (ctyp_equal result_ctyp CT_unit)
          then (
            let table = sprintf "sail_const_arms_%d" !constant_table_counter in
            incr constant_table_counter;
            let values = List.map (fun (_, _, value) -> value) constant_arms in
            let element_type, entry_of, read_statements, read_declares =
              match packed_constant_layout values with
              | Some layout ->
                  let total_width =
                    native_c_integer_width (List.fold_left (fun total (_, width, _) -> total + width) 0 layout)
                  in
                  let element_type = sprintf "uint%d_t" total_width in
                  let entry_of value =
                    sprintf "UINT%d_C(%s)" total_width (Big_int.to_string (packed_constant_entry layout value))
                  in
                  let read exit_of =
                    sprintf "const %s entry = %s[%s];" element_type table selector
                    :: exit_of (packed_constant_unpack result_ctyp layout "entry")
                  in
                  (element_type, entry_of, read, true)
              | None ->
                  let read exit_of = exit_of (sprintf "%s[%s]" table selector) in
                  (sgen_ctyp result_ctyp, sgen_constant_table_initializer, read, false)
            in
            let table_read ~in_switch =
              let exit_of expression =
                match first_exit with
                | Constant_arm_return -> [sprintf "return %s;" expression]
                | Constant_arm_copy (l, destination, label) ->
                    sprintf "%s = %s;" (sgen_clexp_pure l destination) expression
                    ::
                    ( match label with
                    | Some target -> [sprintf "goto %s;" target]
                    | None -> if in_switch then ["break;"] else []
                    )
              in
              read_statements exit_of
            in
            let entries =
              List.concat_map (fun (labels, _, value) -> List.map (fun label -> (label, value)) labels) constant_arms
            in
            let table_declaration =
              string (sprintf "  static const %s %s[] = {" element_type table)
              ^^ nest 2
                   (List.fold_left
                      (fun doc (label, value) ->
                        doc ^^ hardline ^^ string (sprintf "  [%s] = %s," label (entry_of value))
                      )
                      empty entries
                   )
              ^^ hardline ^^ string "  };"
            in
            Some { table_declaration; table_read; table_read_declares = read_declares; residual_cases }
          )
          else None
      | _ -> None
    )

  let rec codegen_instr fid ctx (I_aux (instr, (_, l))) =
    match instr with
    | I_decl (ctyp, id) when is_stack_ctyp ctx ctyp -> ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
    | I_decl (ctyp, id) ->
        ksprintf string "  %s %s;" (sgen_ctyp ctyp) (sgen_name id)
        ^^ hardline
        ^^ sail_create ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_copy (clexp, cval) -> codegen_conversion l ctx clexp cval
    | I_jump (cval, label) -> ksprintf string "  if (%s) {\n    goto %s;\n  }" (sgen_condition cval) label
    | I_if (V_lit (VL_bool condition, CT_bool), then_instrs, else_instrs) ->
        codegen_instrs fid ctx (if condition then then_instrs else else_instrs)
    | I_if (_, [], []) -> empty
    | I_if (cval, [], else_instrs) -> codegen_instr fid ctx (iif l (V_call (Bnot, [cval])) else_instrs [])
    | I_if (cval, [then_instr], []) ->
        ksprintf string "  if (%s)" (sgen_condition cval)
        ^^ space ^^ lbrace
        ^^ nest 2 (hardline ^^ codegen_instr fid ctx then_instr)
        ^^ hardline ^^ twice space ^^ rbrace
    | I_if (cval, then_instrs, []) ->
        string "  if" ^^ space
        ^^ parens (string (sgen_condition cval))
        ^^ space ^^ lbrace
        ^^ nest 2 (hardline ^^ codegen_instrs fid ctx then_instrs)
        ^^ hardline ^^ twice space ^^ rbrace
    | I_if
        ( condition,
          [I_aux (I_copy (then_destination, then_value), _)],
          [I_aux (I_copy (else_destination, else_value), _)]
        )
      when Option.is_some
             (conditional_assignment_expression ctx condition then_destination then_value else_destination else_value)
      ->
        ksprintf string "  %s = %s;" (sgen_clexp_pure l then_destination)
          (Option.get
             (conditional_assignment_expression ctx condition then_destination then_value else_destination else_value)
          )
    | I_if (cval, then_instrs, else_instrs) as original_if -> (
        match collect_switch_cases ctx None None [] original_if with
        | Some (selector, family, (_ :: _ as cases), default_body) ->
            codegen_collected_switch fid ctx selector family cases default_body
        | _ ->
            let codegen_branch instrs =
              lbrace ^^ nest 2 (hardline ^^ codegen_instrs fid ctx instrs) ^^ hardline ^^ twice space ^^ rbrace
            in
            let rec codegen_if cval then_instrs else_instrs =
              match else_instrs with
              | [I_aux (I_if (else_i, else_t, else_e), _)] ->
                  string "if" ^^ space
                  ^^ parens (string (sgen_condition cval))
                  ^^ space ^^ codegen_branch then_instrs ^^ space ^^ string "else" ^^ space
                  ^^ codegen_if else_i else_t else_e
              | _ ->
                  string "if" ^^ space
                  ^^ parens (string (sgen_condition cval))
                  ^^ space ^^ codegen_branch then_instrs ^^ space ^^ string "else" ^^ space
                  ^^ codegen_branch else_instrs
            in
            twice space ^^ codegen_if cval then_instrs else_instrs
      )
    | I_block instrs -> string "  {" ^^ jump 2 2 (codegen_instrs fid ctx instrs) ^^ hardline ^^ string "  }"
    | I_try_block instrs ->
        string "  { /* try */" ^^ jump 2 2 (codegen_instrs fid ctx instrs) ^^ hardline ^^ string "  }"
    | I_funcall (x, extern_info, f, args) ->
        let special_extern = match extern_info with Extern _ -> true | Call _ -> false in
        let x =
          match x with
          | CR_one x -> x
          | CR_multi _ -> Reporting.unreachable l __POS__ "Multiple returns should not exist in C backend"
        in
        let args =
          if erase_unit_values && not (is_variant_constructor ctx (fst f)) then
            List.filter (fun arg -> not (ctyp_equal (cval_ctyp arg) CT_unit)) args
          else args
        in
        let default_c_args = Util.string_of_list ", " sgen_cval_in_value_context args in
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
                  | Some _ -> sprintf "u256_from_%s" (sgen_ctyp_name (cval_ctyp arg))
                  | None -> c_error "native from_bytes_le specialization without fixed-byte argument"
                )
              | None -> c_error "native from_bytes_le specialization without fixed-byte argument"
            )
          | "__sail_to_bytes_le_u256_fixed", ctyp when is_c_repr_fixed_bytes ctyp ->
              sprintf "%s_from_u256" (sgen_ctyp_name ctyp)
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
        (* --c-register-file-thread: a threaded callee takes the register-file
           base as its leading argument.  A threaded caller forwards its own
           [regs] parameter; every other context materializes the global's
           address, so the pointer always equals [&model_registers]. *)
        let regs_argument =
          if (not is_extern) && register_file_threaded_function (fst f) then
            if !current_function_threaded then register_file_param else "&" ^ register_file_variable
          else ""
        in
        let with_regs_argument arguments =
          if regs_argument = "" then arguments
          else if arguments = "" then regs_argument
          else regs_argument ^ ", " ^ arguments
        in
        current_static_helper_demands := Util.StringSet.add fname !current_static_helper_demands;
        if is_extern && raw_fname <> "__sail_fixed_assert" && fname <> "reg_deref" then
          emitted_external_functions := Util.StringSet.add fname !emitted_external_functions;
        if raw_fname = "__sail_byte_pointer_diff" then (
          match args with
          | [left; right] when is_c_repr_byte_pointer (cval_ctyp left) && ctyp_equal (cval_ctyp left) (cval_ctyp right)
            ->
              if match x with CL_id (Return _, _) -> true | _ -> false then
                ksprintf string "  return (%s)(%s - %s);" (sgen_ctyp ctyp) (sgen_cval left) (sgen_cval right)
              else
                ksprintf string "  %s = (%s)(%s - %s);" (sgen_stack_call_destination l ctyp x) (sgen_ctyp ctyp)
                  (sgen_cval left) (sgen_cval right)
          | _ -> c_error ~loc:l "byte-pointer difference marker with incompatible operands"
        )
        else if raw_fname = "__sail_fixed_assert" then (
          let failed condition =
            match condition with
            | V_lit (VL_bool _, _) -> "(!(" ^ sgen_cval condition ^ "))"
            | _ ->
                let expression = sgen_call Bnot [condition] in
                let length = String.length expression in
                if length >= 2 && expression.[0] = '(' && expression.[length - 1] = ')' then expression
                else "(" ^ expression ^ ")"
          in
          match (args, x) with
          | [V_lit (VL_bool false, _)], _ -> string "  __builtin_trap();"
          | [condition], CL_void _ -> ksprintf string "  if %s {\n    __builtin_trap();\n  }" (failed condition)
          | [condition], CL_id (Return _, _) when erase_unit_values && ctyp_equal ctyp CT_unit ->
              ksprintf string "  if %s {\n    __builtin_trap();\n  }\n  return;" (failed condition)
          | [condition], CL_id (Return _, _) ->
              ksprintf string "  if %s {\n    __builtin_trap();\n  }\n  return UNIT;" (failed condition)
          | [condition], _ when erase_unit_values && ctyp_equal ctyp CT_unit ->
              ksprintf string "  if %s {\n    __builtin_trap();\n  }" (failed condition)
          | [condition], _ ->
              ksprintf string "  if %s {\n    __builtin_trap();\n  }\n  %s = UNIT;" (failed condition)
                (sgen_stack_call_destination l ctyp x)
          | _ -> c_error ~loc:l "fixed assertion marker with bad arity"
        )
        else if raw_fname = "fatal_error" then (
          match args with
          | [_] -> string (Printf.sprintf "  fatal_error(%s);" c_args)
          | _ -> c_error ~loc:l "fatal_error with bad arity"
        )
        else if fname = "reg_deref" then
          if match x with CL_id (Return _, _) -> true | _ -> false then ksprintf string "  return *(%s);" c_args
          else if is_stack_ctyp ctx ctyp then
            ksprintf string "  %s = *(%s);" (sgen_stack_call_destination l ctyp x) c_args
          else sail_copy ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s, *(%s)" (sgen_clexp_pure l x) c_args
        else if match x with CL_void _ -> true | _ -> false then
          string (Printf.sprintf "  %s(%s%s);" fname (extra_arguments is_extern) (with_regs_argument c_args))
        else if erase_unit_values && ctyp_equal ctyp CT_unit then
          if match x with CL_id (Return _, _) -> true | _ -> false then
            string (Printf.sprintf "  %s(%s%s);" fname (extra_arguments is_extern) (with_regs_argument c_args))
            ^^ hardline ^^ string "  return;"
          else string (Printf.sprintf "  %s(%s%s);" fname (extra_arguments is_extern) (with_regs_argument c_args))
        else if match x with CL_id (Return _, _) -> true | _ -> false then
          string (Printf.sprintf "  return %s(%s%s);" fname (extra_arguments is_extern) (with_regs_argument c_args))
        else if is_stack_ctyp ctx ctyp then
          string
            (Printf.sprintf "  %s = %s(%s%s);" (sgen_stack_call_destination l ctyp x) fname (extra_arguments is_extern)
               (with_regs_argument c_args)
            )
        else
          string
            (Printf.sprintf "  %s(%s%s, %s);" fname (extra_arguments is_extern)
               (with_regs_argument (sgen_clexp l x))
               c_args
            )
    | I_clear (ctyp, _) when is_stack_ctyp ctx ctyp -> empty
    | I_clear (ctyp, id) -> sail_kill ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_init (ctyp, id, init) -> (
        match init with
        | Init_cval cval
          when Config.optimized_model && (not Config.cpp) && is_stack_ctyp ctx ctyp
               && Option.is_some (stack_conversion_initializer ctyp cval) ->
            ksprintf string "  %s %s = %s;" (sgen_ctyp ctyp) (sgen_name id)
              (Option.get (stack_conversion_initializer ctyp cval))
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
    | I_reinit (ctyp, id, cval)
      when Config.optimized_model && (not Config.cpp) && is_stack_ctyp ctx ctyp
           && Option.is_some (stack_conversion_initializer ctyp cval) ->
        ksprintf string "  %s %s = %s;" (sgen_ctyp ctyp) (sgen_name id)
          (Option.get (stack_conversion_initializer ctyp cval))
    | I_reinit (ctyp, id, cval) ->
        codegen_instr fid ctx (ireset l ctyp id) ^^ hardline ^^ codegen_conversion l ctx (CL_id (id, ctyp)) cval
    | I_reset (ctyp, id) when is_stack_ctyp ctx ctyp ->
        string (Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_name id))
    | I_reset (ctyp, id) -> sail_recreate ~prefix:"  " ~suffix:";" (sgen_ctyp_name ctyp) "&%s" (sgen_name id)
    | I_return cval when erase_unit_values && ctyp_equal (cval_ctyp cval) CT_unit -> string "  return;"
    | I_return cval -> twice space ^^ c_return (string (sgen_cval_in_value_context cval))
    | I_throw _ -> c_error ~loc:l "I_throw reached code generator"
    | I_undefined ctyp ->
        let rec codegen_exn_return ctyp =
          match ctyp with
          | ctyp when is_c_repr_byte_pointer ctyp -> ("NULL", [])
          | ctyp when is_c_repr_u320 ctyp -> ("u320_zero()", [])
          | ctyp when is_c_repr_u256 ctyp -> ("u256_zero()", [])
          | ctyp when is_c_repr_fixed_bytes ctyp -> (sprintf "%s_zero()" (sgen_ctyp_name ctyp), [])
          | CT_unit when erase_unit_values -> ("", [])
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
              (sgen_name gs, [sprintf "struct %s %s = {0};" (sgen_ctyp_name ctyp) (sgen_name gs)])
          | CT_fvector _ when is_stack_ctyp ctx ctyp ->
              let gs = ngensym () in
              (sgen_name gs, [sprintf "%s %s = {0};" (sgen_ctyp ctyp) (sgen_name gs)])
          | CT_ref _ -> ("NULL", [])
          | ctyp -> c_error ("Cannot create undefined value for type: " ^ string_of_ctyp ctyp)
        in
        let ret, prev = codegen_exn_return ctyp in
        separate_map hardline (fun str -> string ("  " ^ str)) (List.rev prev)
        ^^ hardline
        ^^ string
             (if erase_unit_values && ctyp_equal ctyp CT_unit then "  return;" else Printf.sprintf "  return %s;" ret)
    | I_comment str -> string ("  /* " ^ str ^ " */")
    | I_label str -> string (str ^ ": ;")
    | I_goto str -> string (Printf.sprintf "  goto %s;" str)
    | I_raw _ when ctx.no_raw -> empty
    | I_raw str -> string ("  " ^ str)
    | I_end _ -> assert false
    | I_exit _ -> string ("  sail_match_failure(\"" ^ String.escaped (string_of_id fid) ^ "\");")

  and codegen_collected_switch ?(function_tail = false) fid ctx selector family cases default_body =
    (* JIB appends [/* complete */] to the final arm of an exhaustive match.
       Once that match has been recovered as a C switch, the marker conveys no
       information and can make otherwise identical arms appear distinct to
       both readers and [bugprone-branch-clone]. *)
    let remove_completion_marker = List.filter (function I_aux (I_comment "complete", _) -> false | _ -> true) in
    let needs_case_scope = List.exists (function I_aux ((I_decl _ | I_init _), _) -> true | _ -> false) in
    let codegen_case_body body =
      let body = remove_completion_marker body in
      let terminator =
        if switch_branch_exits ctx body then empty
        else hardline ^^ string (if function_tail then "  return;" else "  break;")
      in
      if needs_case_scope body then
        hardline ^^ string "  {"
        ^^ nest 2 (hardline ^^ codegen_instrs fid ctx body ^^ terminator)
        ^^ hardline ^^ string "  }"
      else nest 2 (hardline ^^ codegen_instrs fid ctx body ^^ terminator)
    in
    let covered =
      List.fold_left
        (fun covered (labels, _) ->
          List.fold_left (fun covered label -> Util.StringSet.add label covered) covered labels
        )
        Util.StringSet.empty cases
    in
    let remaining = List.filter (fun label -> not (Util.StringSet.mem label covered)) family in
    let cases = if remaining = [] then cases else cases @ [(remaining, default_body)] in
    let render_case_labels cases =
      let rendered_cases =
        List.map
          (fun (labels, body) ->
            let body_doc = codegen_case_body body in
            (labels, body_doc, Document.to_string body_doc)
          )
          cases
      in
      let merged_cases =
        List.fold_left
          (fun merged (labels, body_doc, key) ->
            let rec merge reversed = function
              | [] -> List.rev_append reversed [(labels, body_doc, key)]
              | (prior_labels, prior_doc, prior_key) :: rest when String.equal key prior_key ->
                  List.rev_append reversed ((prior_labels @ labels, prior_doc, prior_key) :: rest)
              | prior :: rest -> merge (prior :: reversed) rest
            in
            merge [] merged
          )
          [] rendered_cases
      in
      let codegen_case (labels, body, _) =
        separate_map hardline (fun label -> string "  case" ^^ space ^^ string label ^^ colon) labels ^^ body
      in
      separate_map hardline codegen_case merged_cases
    in
    match collected_switch_constant_table ctx selector cases with
    | Some lowering ->
        let read_doc in_switch =
          let statements = separate_map hardline (fun line -> string ("  " ^ line)) (lowering.table_read ~in_switch) in
          if not in_switch then statements
          else if lowering.table_read_declares then
            hardline ^^ string "  {" ^^ nest 2 (hardline ^^ statements) ^^ hardline ^^ string "  }"
          else nest 2 (hardline ^^ statements)
        in
        lowering.table_declaration ^^ hardline
        ^^
        if lowering.residual_cases = [] then read_doc false
        else
          string "  switch" ^^ space
          ^^ parens (string selector)
          ^^ space ^^ lbrace ^^ hardline
          ^^ render_case_labels lowering.residual_cases
          ^^ hardline ^^ string "  default:" ^^ read_doc true ^^ hardline ^^ string "  }"
    | None ->
        string "  switch" ^^ space
        ^^ parens (string selector)
        ^^ space ^^ lbrace ^^ hardline ^^ render_case_labels cases ^^ hardline ^^ string "  }"

  and codegen_instrs ?(function_tail = false) fid ctx instrs =
    let split_simple_loop loop_label end_label instrs =
      let rec split reversed = function
        | I_aux (I_goto back_edge, _) :: I_aux (I_label end_target, _) :: rest
          when String.equal back_edge loop_label && String.equal end_target end_label ->
            Some (List.rev reversed, rest)
        | instr :: rest -> split (instr :: reversed) rest
        | [] -> None
      in
      split [] instrs
    in
    let references_label target instrs =
      List.exists
        (fun instr ->
          let found = ref false in
          ignore
            (map_instr
               (fun (I_aux (aux, _) as sub) ->
                 ( match aux with
                 | (I_goto label | I_jump (_, label)) when String.equal label target -> found := true
                 | _ -> ()
                 );
                 sub
               )
               instr
            );
          !found
        )
        instrs
    in
    let split_loop_header instrs =
      let rec split reversed = function
        | I_aux (I_jump (condition, end_label), _) :: rest -> Some (List.rev reversed, condition, end_label, rest)
        | instr :: rest -> split (instr :: reversed) rest
        | [] -> None
      in
      split [] instrs
    in
    let rec docs = function
      | I_aux (I_if (_, _, []), _) :: _ as terminal_ladder -> (
          match collect_terminal_switch_cases ctx function_tail None None [] terminal_ladder with
          | Some (selector, family, (_ :: _ as cases), default_body) ->
              [codegen_collected_switch ~function_tail fid ctx selector family cases default_body]
          | _ ->
              let first = List.hd terminal_ladder in
              codegen_instr fid ctx first :: docs (List.tl terminal_ladder)
        )
      (* A Sail [foreach] reaches JIB as a label followed by an exit jump,
         a body, and a private back edge.  Recover that region as a C loop.
         The loop setup and induction update remain ordinary typed JIB
         statements, while the structured loop prevents its exit edge from
         jumping across body-local initializers. *)
      | (I_aux (I_label loop_label, _) as loop_instruction)
        :: (I_aux (I_jump (exit_condition, end_label), _) as exit_jump)
        :: tail -> (
          match split_simple_loop loop_label end_label tail with
          | Some (body, rest)
            when (not (references_label loop_label body))
                 && (not (references_label end_label body))
                 && (not (references_label loop_label rest))
                 && not (references_label end_label rest) ->
              (string "  while" ^^ space
              ^^ parens (string (sgen_condition (V_call (Bnot, [exit_condition]))))
              ^^ space ^^ lbrace
              ^^ nest 2 (hardline ^^ codegen_instrs fid ctx body)
              ^^ hardline ^^ twice space ^^ rbrace
              )
              :: docs rest
          | _ -> codegen_instr fid ctx loop_instruction :: docs (exit_jump :: tail)
        )
      (* JIB represents a Sail [while] as a private label, a condition
         temporary, an exit jump, and a back edge.  When neither label is
         referenced from the body, recover the source loop at emission time.
         This keeps declarations inside the C loop body, so the exit edge does
         not jump across their initializers, and removes the administrative
         boolean temporary entirely. *)
      | (I_aux (I_decl (CT_bool, declared), _) as declaration)
        :: (I_aux (I_label loop_label, _) as loop_instruction)
        :: (I_aux (I_copy (CL_id (assigned, assigned_ctyp), condition), _) as condition_copy)
        :: (I_aux (I_jump (V_call (Bnot, [V_id (tested, tested_ctyp)]), end_label), _) as exit_jump)
        :: tail
        when Name.compare declared assigned = 0
             && Name.compare declared tested = 0
             && ctyp_equal assigned_ctyp CT_bool && ctyp_equal tested_ctyp CT_bool
             && ctyp_equal (cval_ctyp condition) CT_bool -> (
          match split_simple_loop loop_label end_label tail with
          | Some (body, rest)
            when (not (references_label loop_label body))
                 && (not (references_label end_label body))
                 && (not (references_label loop_label rest))
                 && (not (references_label end_label rest))
                 && not (List.exists (fun instr -> instr_references ~read:declared ~direct:false instr) (body @ rest))
            ->
              (string "  while" ^^ space
              ^^ parens (string (sgen_condition condition))
              ^^ space ^^ lbrace
              ^^ nest 2 (hardline ^^ codegen_instrs fid ctx body)
              ^^ hardline ^^ twice space ^^ rbrace
              )
              :: docs rest
          | _ -> codegen_instr fid ctx declaration :: docs (loop_instruction :: condition_copy :: exit_jump :: tail)
        )
      (* A non-trivial [while] condition can contain pure calls and short-
         circuit control flow before its exit jump.  Keep those typed JIB
         statements in the loop header and replace the private back edge with
         a structured infinite loop plus [break].  The administrative result
         declaration moves into the loop because it is not loop-carried. *)
      | (I_aux (I_decl (CT_bool, declared), _) as declaration)
        :: (I_aux (I_label loop_label, _) as loop_instruction)
        :: tail -> (
          match split_loop_header tail with
          | Some (header, exit_condition, end_label, after_jump) -> (
              match split_simple_loop loop_label end_label after_jump with
              | Some (body, rest)
                when (not (references_label loop_label header))
                     && (not (references_label end_label header))
                     && (not (references_label loop_label body))
                     && (not (references_label end_label body))
                     && (not (references_label loop_label rest))
                     && (not (references_label end_label rest))
                     && not
                          (List.exists (fun instr -> instr_references ~read:declared ~direct:false instr) (body @ rest))
                ->
                  (string "  while (true)" ^^ space ^^ lbrace
                  ^^ nest 2
                       (hardline
                       ^^ codegen_instrs fid ctx (declaration :: header)
                       ^^ hardline
                       ^^ ksprintf string "  if (%s) {" (sgen_condition exit_condition)
                       ^^ hardline ^^ string "    break;" ^^ hardline ^^ string "  }" ^^ hardline
                       ^^ codegen_instrs fid ctx body
                       )
                  ^^ hardline ^^ twice space ^^ rbrace
                  )
                  :: docs rest
              | _ -> codegen_instr fid ctx declaration :: docs (loop_instruction :: tail)
            )
          | None -> codegen_instr fid ctx declaration :: docs (loop_instruction :: tail)
        )
      (* Stack clears have no generated C representation.  Drop them before
         matching adjacent source operations so an invisible lifetime marker
         cannot prevent declaration/return folding.  The JIB optimizer already
         removes these in ordinary bodies, but later specialization cleanup can
         expose another one immediately before emission. *)
      | instr :: I_aux (I_clear (ctyp, _), _) :: rest when is_stack_ctyp ctx ctyp -> docs (instr :: rest)
      | I_aux (I_clear (ctyp, _), _) :: rest when is_stack_ctyp ctx ctyp -> docs rest
      (* A try expression writes its result only on the normal or handled
         paths.  An unhandled exception deliberately returns through the C
         exception ABI with that value unread by the caller, but reading an
         indeterminate scalar in the generated return statement is still C
         undefined behaviour.  Give only the try-result local a zero fallback;
         ordinary adjacent declarations continue to use their real
         initializer below. *)
      | I_aux (I_decl (declared_ctyp, declared), _) :: (I_aux (I_try_block _, _) as try_block) :: rest
        when Config.optimized_model && (not Config.cpp) && is_stack_ctyp ctx declared_ctyp ->
          ksprintf string "  %s %s = {0};" (sgen_ctyp declared_ctyp) (sgen_name declared)
          :: codegen_instr fid ctx try_block :: docs rest
      (* A Sail value conditional reaches JIB as a declaration followed by
         two pure copies into the same local.  When both conversions are valid
         initializer expressions, retain that source expression directly as
         one C conditional initializer.  Checked conversions and non-stack
         values deliberately remain structured control flow. *)
      | I_aux (I_decl (declared_ctyp, declared), _)
        :: I_aux
             ( I_if
                 ( condition,
                   [I_aux (I_copy (then_destination, then_value), _)],
                   [I_aux (I_copy (else_destination, else_value), _)]
                 ),
               _
             )
        :: rest
        when Config.optimized_model && (not Config.cpp) && is_stack_ctyp ctx declared_ctyp
             && ( match then_destination with
               | CL_id (destination, destination_ctyp) ->
                   Name.compare declared destination = 0 && ctyp_equal declared_ctyp destination_ctyp
               | _ -> false
               )
             && Option.is_some
                  (conditional_assignment_expression ctx condition then_destination then_value else_destination
                     else_value
                  ) ->
          ksprintf string "  %s %s = %s;" (sgen_ctyp declared_ctyp) (sgen_name declared)
            (Option.get
               (conditional_assignment_expression ctx condition then_destination then_value else_destination else_value)
            )
          :: docs rest
      (* [fatal_error] is the C model's concrete noreturn boundary.
         Sail's following [exit(())] exists only to give the source expression
         the required result type; JIB lowers that bridge to [I_exit].  Once
         the fatal call is adjacent, emitting a second abort is unreachable
         noise and obscures the intended C control flow. *)
      | (I_aux (I_funcall (_, _, callee, _), _) as fatal_call) :: I_aux (I_exit _, _) :: rest
        when String.equal (string_of_id (fst callee)) "fatal_error" ->
          codegen_instr fid ctx fatal_call :: docs rest
      | I_aux (I_init (initialized_ctyp, initialized, Init_cval value), _)
        :: I_aux (I_return (V_id (result, result_ctyp)), _)
        :: rest
        when Config.optimized_model && (not Config.cpp) && is_stack_ctyp ctx initialized_ctyp
             && Name.compare initialized result = 0
             && ctyp_equal initialized_ctyp result_ctyp
             && Option.is_some (stack_conversion_initializer initialized_ctyp value) ->
          ksprintf string "  return %s;" (Option.get (stack_conversion_initializer initialized_ctyp value)) :: docs rest
      | I_aux (I_reinit (initialized_ctyp, initialized, value), _)
        :: I_aux (I_return (V_id (result, result_ctyp)), _)
        :: rest
        when Config.optimized_model && (not Config.cpp) && is_stack_ctyp ctx initialized_ctyp
             && Name.compare initialized result = 0
             && ctyp_equal initialized_ctyp result_ctyp
             && Option.is_some (stack_conversion_initializer initialized_ctyp value) ->
          ksprintf string "  return %s;" (Option.get (stack_conversion_initializer initialized_ctyp value)) :: docs rest
      | I_aux (I_decl (declared_ctyp, declared), _)
        :: I_aux (I_copy (CL_id (destination, destination_ctyp), value), (_, conversion_location))
        :: rest
        when Config.optimized_model && (not Config.cpp) && is_c_repr_fixed_bytes declared_ctyp
             && Name.compare declared destination = 0
             && ctyp_equal declared_ctyp destination_ctyp
             &&
             match cval_ctyp value with
             | CT_vector (CT_fbits 8 | CT_fuint 8) | CT_fvector (_, (CT_fbits 8 | CT_fuint 8)) -> true
             | _ -> false ->
          (ksprintf string "  %s %s = {0};" (sgen_ctyp declared_ctyp) (sgen_name declared)
          ^^ hardline
          ^^ codegen_fixed_bytes_vector_conversion conversion_location
               (CL_id (destination, destination_ctyp))
               value declared_ctyp ~initialize:false
          )
          :: docs rest
      | I_aux (I_decl (declared_ctyp, declared), _)
        :: I_aux (I_copy (CL_id (destination, destination_ctyp), value), _)
        :: I_aux (I_return (V_id (result, result_ctyp)), _)
        :: rest
        when Config.optimized_model && (not Config.cpp) && is_stack_ctyp ctx declared_ctyp
             && Name.compare declared destination = 0
             && Name.compare declared result = 0
             && ctyp_equal declared_ctyp result_ctyp
             && stack_call_initializer_compatible declared_ctyp destination_ctyp
             && Option.is_some (stack_conversion_initializer destination_ctyp value) ->
          ksprintf string "  return %s;" (Option.get (stack_conversion_initializer destination_ctyp value)) :: docs rest
      | I_aux (I_decl (declared_ctyp, declared), _)
        :: I_aux (I_copy (CL_id (destination, destination_ctyp), value), _)
        :: rest
        when Config.optimized_model && (not Config.cpp) && is_stack_ctyp ctx declared_ctyp
             && Name.compare declared destination = 0
             && stack_call_initializer_compatible declared_ctyp destination_ctyp
             && Option.is_some (stack_conversion_initializer destination_ctyp value) ->
          ksprintf string "  %s %s = %s;" (sgen_ctyp declared_ctyp) (sgen_name declared)
            (Option.get (stack_conversion_initializer destination_ctyp value))
          :: docs rest
      | I_aux (I_decl (declared_ctyp, declared), _)
        :: (I_aux (I_funcall (CR_one (CL_id (destination, destination_ctyp)), _, _, _), _) as call)
        :: rest
        when Config.optimized_model && (not Config.cpp) && is_stack_ctyp ctx declared_ctyp
             && Name.compare declared destination = 0
             && stack_call_initializer_compatible declared_ctyp destination_ctyp ->
          let previous = !stack_call_initializer in
          stack_call_initializer := Some (declared, declared_ctyp);
          let call_doc = codegen_instr fid ctx call in
          stack_call_initializer := previous;
          call_doc :: docs rest
      | instr :: rest -> codegen_instr fid ctx instr :: docs rest
      | [] -> []
    in
    separate hardline (squash_empty (docs instrs))

  let emit_optimized_exception_state = ref true

  let static_type_helper_return return =
    if Config.optimized_model then "static inline " ^ return else "static " ^ return

  let codegen_type_def ctx =
    let open Printf in
    function
    | CTD_variant (id, _, _)
      when Config.optimized_model && (not !emit_optimized_exception_state) && String.equal (string_of_id id) "exception"
      ->
        (* Sail keeps a dummy exception union even when the model has no
           language-level throws.  The optimized EVM model uses the explicit
           noreturn [fatal_error] boundary and represents recoverable EVM
           halts as ordinary data, so this otherwise contributes only dead
           current_exception/have_exception ABI state. *)
        []
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
                  [codegen_instrs (mk_id "set_abstract") ctx init]
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
          c_function ~return:(static_type_helper_return "bool")
            (sail_equal enum_name "enum %s op1, enum %s op2" enum_name enum_name)
            [c_stmt "return (bool)(op1 == op2)"]
        in
        let enum_undefined =
          let name = sgen_id id in
          let parameter = if Config.optimized_model then "void" else "unit u" in
          string
            (Printf.sprintf "%s UNDEFINED(%s)(%s) { return %s; }"
               (static_type_helper_return ("enum " ^ name))
               name parameter (sgen_id first_id)
            )
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
    | CTD_abbrev (_, _) when Config.optimized_model ->
        (* Transparent source aliases do not own optimized-C type identity.
           [$[c_repr]] selects the concrete ABI carrier; semantic aliases such
           as [word], [hash], or [address] are erased after type checking. *)
        []
    | CTD_abbrev (id, ctyp) ->
        let underlying = sgen_ctyp ctyp in
        [
          TypeDeclaration
            (ksprintf string "// type abbreviation %s" (string_of_id id)
            ^^ hardline
            ^^ separate space [string "typedef"; string underlying; codegen_id id]
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
          c_function ~return:(static_type_helper_return "void")
            (sail_copy struct_name "struct %s *rop, const struct %s op" struct_name struct_name)
            (List.map set_field ctors)
        in
        (* Derive the various lifecycle functions create/recreate/kill for the struct *)
        let derive (f : string -> ('a, unit, string, document) format4 -> 'a) =
          let per_field (field_id, ctyp) =
            if not (is_stack_ctyp ctx ctyp) then [f (sgen_ctyp_name ctyp) "&op->%s" (sgen_id field_id) ^^ semi] else []
          in
          c_function ~return:(static_type_helper_return "void")
            (f struct_name "struct %s *op" struct_name)
            (List.concat (List.map per_field ctors))
        in
        let struct_eq =
          let field_eq (field_id, ctyp) =
            let field = sgen_id field_id in
            codegen_equal ctyp (sprintf "op1.%s" field) (sprintf "op2.%s" field)
          in
          let equality =
            match ctors with
            | [(field_id, ctyp)] ->
                let field = sgen_id field_id in
                codegen_equal_in_bool_value ctyp (sprintf "op1.%s" field) (sprintf "op2.%s" field)
            | _ -> string "(bool)(" ^^ separate_map (string " && ") field_eq ctors ^^ string ")"
          in
          c_function ~return:(static_type_helper_return "bool")
            (sail_equal (sgen_id id) "struct %s op1, struct %s op2" (sgen_id id) (sgen_id id))
            [string "return" ^^ space ^^ equality ^^ semi]
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
        @ ( if Config.optimized_model && is_stack_ctyp ctx struct_ctyp then []
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
          c_function ~return:(static_type_helper_return "void") (sail_create n "struct %s *op" n)
            ([string (Printf.sprintf "op->kind = Kind_%s;" (sgen_id ctor_id))]
            @
            if not (is_stack_ctyp ctx ctyp) then
              [sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&op->variants.%s" (sgen_id ctor_id)]
            else []
            )
        in
        let codegen_reinit =
          let n = sgen_id id in
          c_function ~return:(static_type_helper_return "void") (sail_recreate n "struct %s *op" n) []
        in
        let clear_field v ctor_id ctyp =
          if is_stack_ctyp ctx ctyp then None
          else Some (sail_kill ~suffix:";" (sgen_ctyp_name ctyp) "&%s->variants.%s" v (sgen_id ctor_id))
        in
        let codegen_clear =
          let n = sgen_id id in
          c_function ~return:(static_type_helper_return "void") (sail_kill n "struct %s *op" n)
            [each_ctor "op->" (clear_field "op") tus]
        in
        let codegen_ctor (ctor_id, ctyp) =
          let ctor_args = Printf.sprintf "%s op" (sgen_const_ctyp ctyp) in
          if Config.optimized_model && stack_variant then (
            let n = sgen_id id in
            c_function
              ~return:(static_type_helper_return ("struct " ^ n))
              (ksprintf string "%s(%s%s)" (sgen_function_id ctor_id) (extra_params ()) ctor_args)
              [
                ksprintf string "struct %s result;" n;
                string ("result.kind = Kind_" ^ sgen_id ctor_id) ^^ semi;
                ksprintf string "result.variants.%s = op;" (sgen_id ctor_id);
                c_return (string "result");
              ]
          )
          else
            c_function ~return:(static_type_helper_return "void")
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
          c_function ~return:(static_type_helper_return "void")
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
              (codegen_equal_in_bool_value ctyp
                 (sprintf "op1.variants.%s" (sgen_id ctor_id))
                 (sprintf "op2.variants.%s" (sgen_id ctor_id))
              )
          in
          let codegen_eq_tests ctors =
            let unit_ctors, payload_ctors =
              List.partition
                (fun (_, ctyp) -> Config.optimized_model && !optimize_unit_results && ctyp_equal ctyp CT_unit)
                ctors
            in
            let payload_cases =
              List.map
                (fun (ctor_id, ctyp) -> (ksprintf string "Kind_%s" (sgen_id ctor_id), [codegen_eq_test ctor_id ctyp]))
                payload_ctors
            in
            let unit_cases =
              match List.rev unit_ctors with
              | [] -> []
              | (last_ctor_id, _) :: preceding ->
                  List.rev_map (fun (ctor_id, _) -> (ksprintf string "Kind_%s" (sgen_id ctor_id), [])) preceding
                  @ [(ksprintf string "Kind_%s" (sgen_id last_ctor_id), [c_return (string "true")])]
            in
            c_if (ksprintf string "(op1.kind != op2.kind)") [c_return (string "false")]
            ^^ ( match payload_cases @ unit_cases with
              | [] -> empty
              | cases -> hardline ^^ c_switch ~case_break:false (string "(op1.kind)") cases
              )
            ^^ hardline
            ^^ c_return (string "false")
          in
          let n = sgen_id id in
          c_function ~return:(static_type_helper_return "bool")
            (sail_equal n "struct %s op1, struct %s op2" n n)
            [codegen_eq_tests tus]
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
_Noreturn static inline void sail_native_conversion_failure(const char *operation) {
  const int write_status = fprintf(stderr, "Sail C backend: %s\n", operation);
  (void)write_status;
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
typedef struct { uint64_t limbs[2]; } u128;
#endif
|}
      in
      let helpers =
        string
          {|

static inline u128 u128_zero(void) {
  u128 result = {{0}};
  return result;
}

static inline u128 u128_of_u64(const uint64_t value) {
  u128 result = {{value, UINT64_C(0)}};
  return result;
}

static inline uint64_t u128_to_u64(const u128 value) {
  if (value.limbs[1] != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint64_t domain");
  }
  return value.limbs[0];
}

static inline uint64_t u128_extract_u64(const u128 value, const uint64_t start) {
  if (start >= UINT64_C(128)) {
    return UINT64_C(0);
  }
  const size_t limb = (size_t)(start >> 6);
  const unsigned offset = (unsigned)(start & UINT64_C(63));
  uint64_t result = value.limbs[limb] >> offset;
  if (offset != 0 && limb + 1 < 2) {
    result |= value.limbs[limb + 1] << (64 - offset);
  }
  return result;
}

static inline bool eq_u128(const u128 op1, const u128 op2) {
  return (bool)(op1.limbs[0] == op2.limbs[0] && op1.limbs[1] == op2.limbs[1]);
}

static inline bool u128_eq_u64(const u128 lhs, const uint64_t rhs) {
  return (bool)(lhs.limbs[0] == rhs && lhs.limbs[1] == UINT64_C(0));
}

static inline u128 u128_not(const u128 value) {
  u128 result = {{~value.limbs[0], ~value.limbs[1]}};
  return result;
}

static inline u128 u128_and(const u128 lhs, const u128 rhs) {
  u128 result = {{lhs.limbs[0] & rhs.limbs[0], lhs.limbs[1] & rhs.limbs[1]}};
  return result;
}

static inline u128 u128_or(const u128 lhs, const u128 rhs) {
  u128 result = {{lhs.limbs[0] | rhs.limbs[0], lhs.limbs[1] | rhs.limbs[1]}};
  return result;
}

static inline u128 u128_xor(const u128 lhs, const u128 rhs) {
  u128 result = {{lhs.limbs[0] ^ rhs.limbs[0], lhs.limbs[1] ^ rhs.limbs[1]}};
  return result;
}

static inline bool u128_lt(const u128 lhs, const u128 rhs) {
  return (bool)(lhs.limbs[1] != rhs.limbs[1]
      ? lhs.limbs[1] < rhs.limbs[1]
      : lhs.limbs[0] < rhs.limbs[0]);
}

static inline bool u128_lt_u64(const u128 lhs, const uint64_t rhs) {
  return (bool)(lhs.limbs[1] == UINT64_C(0) && lhs.limbs[0] < rhs);
}

static inline bool u64_lt_u128(const uint64_t lhs, const u128 rhs) {
  return (bool)(rhs.limbs[1] != UINT64_C(0) || lhs < rhs.limbs[0]);
}

static inline u128 u128_add(const u128 lhs, const u128 rhs) {
  u128 result;
  result.limbs[0] = lhs.limbs[0] + rhs.limbs[0];
  result.limbs[1] = lhs.limbs[1] + rhs.limbs[1]
                  + (result.limbs[0] < lhs.limbs[0]);
  return result;
}

static inline u128 u128_add_u64(const u128 lhs, const uint64_t rhs) {
  u128 result = lhs;
  result.limbs[0] += rhs;
  result.limbs[1] += result.limbs[0] < lhs.limbs[0];
  return result;
}

static inline u128 u128_add_u64_u64(const uint64_t lhs,
                                         const uint64_t rhs) {
  u128 result = {{lhs + rhs, lhs + rhs < lhs}};
  return result;
}

static inline u128 u128_sub(const u128 lhs, const u128 rhs) {
  u128 result;
  result.limbs[0] = lhs.limbs[0] - rhs.limbs[0];
  result.limbs[1] = lhs.limbs[1] - rhs.limbs[1]
                  - (lhs.limbs[0] < rhs.limbs[0]);
  return result;
}

static inline u128 u128_sub_u64(const u128 lhs, const uint64_t rhs) {
  u128 result = lhs;
  result.limbs[0] -= rhs;
  result.limbs[1] -= lhs.limbs[0] < rhs;
  return result;
}

static inline uint64_t u64_sub_u128(const uint64_t lhs, const u128 rhs) {
  return lhs - rhs.limbs[0];
}

static inline u128 u128_sub_u64_u64(const uint64_t lhs,
                                         const uint64_t rhs) {
  u128 result = {{lhs - rhs, UINT64_C(0)}};
  return result;
}

static inline u128 u128_mul(const u128 lhs, const u128 rhs) {
  const unsigned __int128 low = (unsigned __int128)lhs.limbs[0] * rhs.limbs[0];
  u128 result;
  result.limbs[0] = (uint64_t)low;
  result.limbs[1] = (uint64_t)(low >> 64)
                  + (lhs.limbs[0] * rhs.limbs[1])
                  + (lhs.limbs[1] * rhs.limbs[0]);
  return result;
}

static inline u128 u128_mul_u64(const u128 lhs, const uint64_t rhs) {
  const unsigned __int128 low = (unsigned __int128)lhs.limbs[0] * rhs;
  u128 result;
  result.limbs[0] = (uint64_t)low;
  result.limbs[1] = (uint64_t)(low >> 64) + (lhs.limbs[1] * rhs);
  return result;
}

static inline u128 u128_mul_u64_u64(const uint64_t lhs,
                                         const uint64_t rhs) {
  const unsigned __int128 product = (unsigned __int128)lhs * rhs;
  u128 result = {{(uint64_t)product, (uint64_t)(product >> 64)}};
  return result;
}

static inline bool u128_is_zero(const u128 value) {
  return (value.limbs[0] | value.limbs[1]) == UINT64_C(0);
}

/* Integer division helpers are emitted only for JIB operations carrying the
 * nonzero-divisor proof marker.  Do not re-check that source invariant here:
 * an unproved division remains in Sail's mathematical integer runtime. */
static inline void u128_divrem_u64(const u128 dividend,
                                   const uint64_t divisor,
  u128 *quotient,
                                   uint64_t *remainder) {
  u128 q = {{0}};
  uint64_t r = UINT64_C(0);
  q.limbs[1] = dividend.limbs[1] / divisor;
  r = dividend.limbs[1] % divisor;
  const unsigned __int128 partial =
      ((unsigned __int128)r << 64) | dividend.limbs[0];
  q.limbs[0] = (uint64_t)(partial / divisor);
  r = (uint64_t)(partial % divisor);
  if (quotient != NULL) {
    *quotient = q;
  }
  if (remainder != NULL) {
    *remainder = r;
  }
}

static inline void u128_store_divrem(const u128 quotient_value,
                                     const u128 remainder_value,
                                     u128 *quotient,
                                     u128 *remainder) {
  if (quotient != NULL) {
    *quotient = quotient_value;
  }
  if (remainder != NULL) {
    *remainder = remainder_value;
  }
}

/* Two-limb specialization of normalized Knuth division.  Like ruint, it
 * dispatches the one-limb divisor case separately and computes at most one
 * quotient limb for a normalized two-limb divisor. */
static inline void u128_divrem(const u128 dividend,
                               const u128 divisor,
                               u128 *quotient,
  u128 *remainder) {
  u128 q = {{0}};
  u128 r = {{0}};
  if (divisor.limbs[1] == UINT64_C(0)) {
    uint64_t rem = UINT64_C(0);
    u128_divrem_u64(dividend, divisor.limbs[0], &q, &rem);
    r.limbs[0] = rem;
    u128_store_divrem(q, r, quotient, remainder);
    return;
  }

  if (u128_lt(dividend, divisor)) {
    r = dividend;
    u128_store_divrem(q, r, quotient, remainder);
    return;
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

  const unsigned __int128 p1 = ((unsigned __int128)qhat * v1)
                              + p0_high + borrow0;
  const uint64_t p1_low = (uint64_t)p1;
  const uint64_t p1_high = (uint64_t)(p1 >> 64);
  const uint64_t borrow1 = u1 < p1_low;
  u1 -= p1_low;
  const uint64_t top_subtrahend = p1_high + borrow1;
  const bool top_overflow = top_subtrahend < p1_high;
  const bool negative = (bool)(top_overflow || u2 < top_subtrahend);

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

  u128_store_divrem(q, r, quotient, remainder);
}

static inline u128 u128_div(const u128 lhs, const u128 rhs) {
  u128 result;
  u128_divrem(lhs, rhs, &result, NULL);
  return result;
}

static inline u128 u128_mod(const u128 lhs, const u128 rhs) {
  u128 result;
  u128_divrem(lhs, rhs, NULL, &result);
  return result;
}

static inline u128 u128_div_u64(const u128 lhs, const uint64_t rhs) {
  u128 result;
  u128_divrem_u64(lhs, rhs, &result, NULL);
  return result;
}

static inline u128 u128_mod_u64(const u128 lhs, const uint64_t rhs) {
  uint64_t remainder;
  u128_divrem_u64(lhs, rhs, NULL, &remainder);
  return u128_of_u64(remainder);
}
|}
      in
      let generic_sail_int_helpers =
        string
          {|
static inline u128 u128_of_sail_int(const sail_int value) {
  u128 result = {{0}};
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
typedef struct { uint64_t limbs[2]; } u128;
#endif

#ifndef SAIL_U256_DEFINED
#define SAIL_U256_DEFINED
typedef struct { uint64_t limbs[4]; } u256;
#endif
|}
      in
      let base_helpers =
        string
          {|
static inline u256 u256_zero(void) {
  u256 result = {{0}};
  return result;
}

static inline u256 u256_of_u128(const u128 value) {
  u256 result = {{value.limbs[0], value.limbs[1], UINT64_C(0), UINT64_C(0)}};
  return result;
}

static inline u128 u128_of_u256(const u256 value) {
  if (value.limbs[2] != UINT64_C(0) || value.limbs[3] != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint128_t domain");
  }
  u128 result = {{value.limbs[0], value.limbs[1]}};
  return result;
}

static inline uint64_t u256_to_u64(const u256 value) {
  if (value.limbs[1] != UINT64_C(0)
      || value.limbs[2] != UINT64_C(0)
      || value.limbs[3] != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint64_t domain");
  }
  return value.limbs[0];
}

static inline bool eq_u256(const u256 op1, const u256 op2) {
  return (bool)(op1.limbs[0] == op2.limbs[0]
      && op1.limbs[1] == op2.limbs[1]
      && op1.limbs[2] == op2.limbs[2]
      && op1.limbs[3] == op2.limbs[3]);
}

static inline uint64_t u256_bit(const u256 value, const int64_t index) {
  if (index < 0 || index >= 256) {
    return UINT64_C(0);
  }
  return (value.limbs[(uint64_t)index >> 6] >> ((uint64_t)index & UINT64_C(63))) & UINT64_C(1);
}

static inline uint64_t u256_extract_u64(const u256 value, const uint64_t start) {
  if (start >= UINT64_C(256)) {
    return UINT64_C(0);
  }
  const size_t limb = (size_t)(start >> 6);
  const unsigned offset = (unsigned)(start & UINT64_C(63));
  uint64_t result = value.limbs[limb] >> offset;
  if (offset != 0 && limb + 1 < 4) {
    result |= value.limbs[limb + 1] << (64 - offset);
  }
  return result;
}

static inline u256 u256_update_u64(u256 value, const uint64_t index,
                                        const uint64_t bit) {
  if (index >= UINT64_C(256)) {
    return value;
  }
  const size_t limb = (size_t)(index >> 6);
  const uint64_t mask = UINT64_C(1) << (index & UINT64_C(63));
  if ((bit & UINT64_C(1)) != 0) {
    value.limbs[limb] |= mask;
  } else {
    value.limbs[limb] &= ~mask;
  }
  return value;
}

static inline u256 u256_update_i64(u256 value, const int64_t index,
                                        const uint64_t bit) {
  if (index < INT64_C(0)) {
    return value;
  }
  return u256_update_u64(value, (uint64_t)index, bit);
}

static inline uint64_t fast_vector_access_u256(const u256 value, const int64_t index) {
  return u256_bit(value, index);
}

static inline u256 u256_not(const u256 value) {
  u256 result = {0};
  for (size_t i = 0; i < 4; ++i) {
    result.limbs[i] = ~value.limbs[i];
  }
  return result;
}

static inline u256 u256_and(const u256 lhs, const u256 rhs) {
  u256 result = {0};
  for (size_t i = 0; i < 4; ++i) {
    result.limbs[i] = lhs.limbs[i] & rhs.limbs[i];
  }
  return result;
}

static inline u256 u256_or(const u256 lhs, const u256 rhs) {
  u256 result = {0};
  for (size_t i = 0; i < 4; ++i) {
    result.limbs[i] = lhs.limbs[i] | rhs.limbs[i];
  }
  return result;
}

static inline u256 u256_xor(const u256 lhs, const u256 rhs) {
  u256 result = {0};
  for (size_t i = 0; i < 4; ++i) {
    result.limbs[i] = lhs.limbs[i] ^ rhs.limbs[i];
  }
  return result;
}

static inline u256 u256_add(const u256 lhs, const u256 rhs) {
  u256 result = {0};
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

static inline u256 u256_add_u128_u128(const u128 lhs,
                                           const u128 rhs) {
  u256 result = {{0}};
  const unsigned __int128 low =
      (unsigned __int128)lhs.limbs[0] + rhs.limbs[0];
  result.limbs[0] = (uint64_t)low;
  const unsigned __int128 high =
      (unsigned __int128)lhs.limbs[1] + rhs.limbs[1] + (low >> 64);
  result.limbs[1] = (uint64_t)high;
  result.limbs[2] = (uint64_t)(high >> 64);
  return result;
}

static inline u256 u256_add_u128_u64(const u128 lhs,
                                          const uint64_t rhs) {
  u256 result = {{0}};
  const unsigned __int128 low = (unsigned __int128)lhs.limbs[0] + rhs;
  result.limbs[0] = (uint64_t)low;
  const unsigned __int128 high = (unsigned __int128)lhs.limbs[1] + (low >> 64);
  result.limbs[1] = (uint64_t)high;
  result.limbs[2] = (uint64_t)(high >> 64);
  return result;
}

static inline u256 u256_add_u64_u128(const uint64_t lhs,
                                          const u128 rhs) {
  return u256_add_u128_u64(rhs, lhs);
}

static inline u256 u256_sub(const u256 lhs, const u256 rhs) {
  u256 result = {0};
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

static inline u256 u256_mul(const u256 lhs, const u256 rhs) {
  u256 result = {{0}};
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

static inline u256 u256_mul_u128_u128(const u128 lhs,
                                           const u128 rhs) {
  u256 result = {{0}};
  for (size_t i = 0; i < 2; ++i) {
    unsigned __int128 carry = 0;
    for (size_t j = 0; j < 2; ++j) {
      const size_t k = i + j;
      const unsigned __int128 sum =
          ((unsigned __int128)lhs.limbs[i] * rhs.limbs[j])
          + result.limbs[k] + carry;
      result.limbs[k] = (uint64_t)sum;
      carry = sum >> 64;
    }
    result.limbs[i + 2] = (uint64_t)carry;
  }
  return result;
}

static inline u256 u256_mul_u128_u64(const u128 lhs,
                                          const uint64_t rhs) {
  u256 result = {{0}};
  unsigned __int128 carry = 0;
  for (size_t i = 0; i < 2; ++i) {
    const unsigned __int128 product =
        ((unsigned __int128)lhs.limbs[i] * rhs) + carry;
    result.limbs[i] = (uint64_t)product;
    carry = product >> 64;
  }
  result.limbs[2] = (uint64_t)carry;
  return result;
}

static inline u256 u256_mul_u64_u128(const uint64_t lhs,
                                          const u128 rhs) {
  return u256_mul_u128_u64(rhs, lhs);
}

static inline bool u256_is_zero(const u256 value) {
  return (value.limbs[0] | value.limbs[1] | value.limbs[2] | value.limbs[3])
      == UINT64_C(0);
}

static inline bool u256_lt(const u256 lhs, const u256 rhs) {
  for (size_t i = 4; i-- > 0;) {
    if (lhs.limbs[i] != rhs.limbs[i]) {
      return lhs.limbs[i] < rhs.limbs[i];
    }
  }
  return false;
}

static inline bool u256_eq_u128(const u256 lhs, const u128 rhs) {
  return (bool)(lhs.limbs[0] == rhs.limbs[0]
      && lhs.limbs[1] == rhs.limbs[1]
      && lhs.limbs[2] == UINT64_C(0)
      && lhs.limbs[3] == UINT64_C(0));
}

static inline bool u256_lt_u128(const u256 lhs, const u128 rhs) {
  if ((lhs.limbs[2] | lhs.limbs[3]) != UINT64_C(0)) {
    return false;
  }
  if (lhs.limbs[1] != rhs.limbs[1]) {
    return lhs.limbs[1] < rhs.limbs[1];
  }
  return lhs.limbs[0] < rhs.limbs[0];
}

static inline bool u128_lt_u256(const u128 lhs, const u256 rhs) {
  if ((rhs.limbs[2] | rhs.limbs[3]) != UINT64_C(0)) {
    return true;
  }
  if (lhs.limbs[1] != rhs.limbs[1]) {
    return lhs.limbs[1] < rhs.limbs[1];
  }
  return lhs.limbs[0] < rhs.limbs[0];
}

static inline bool u256_eq_u64(const u256 lhs, const uint64_t rhs) {
  return (bool)(lhs.limbs[0] == rhs
      && lhs.limbs[1] == UINT64_C(0)
      && lhs.limbs[2] == UINT64_C(0)
      && lhs.limbs[3] == UINT64_C(0));
}

static inline bool u256_lt_u64(const u256 lhs, const uint64_t rhs) {
  return (bool)(lhs.limbs[1] == UINT64_C(0)
      && lhs.limbs[2] == UINT64_C(0)
      && lhs.limbs[3] == UINT64_C(0)
      && lhs.limbs[0] < rhs);
}

static inline bool u64_lt_u256(const uint64_t lhs, const u256 rhs) {
  return (bool)(rhs.limbs[1] != UINT64_C(0)
      || rhs.limbs[2] != UINT64_C(0)
      || rhs.limbs[3] != UINT64_C(0)
      || lhs < rhs.limbs[0]);
}

static inline u256 u256_add_u64(const u256 lhs,
                                     const uint64_t rhs) {
  u256 result = lhs;
  result.limbs[0] += rhs;
  uint64_t carry = result.limbs[0] < lhs.limbs[0];
  for (size_t i = 1; i < 4 && carry != UINT64_C(0); ++i) {
    const uint64_t previous = result.limbs[i];
    result.limbs[i]++;
    carry = result.limbs[i] < previous;
  }
  return result;
}

static inline u256 u256_add_u128(const u256 lhs,
                                      const u128 rhs) {
  u256 result = lhs;
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

static inline u256 u256_sub_u64(const u256 lhs,
                                     const uint64_t rhs) {
  u256 result = lhs;
  result.limbs[0] -= rhs;
  uint64_t borrow = lhs.limbs[0] < rhs;
  for (size_t i = 1; i < 4 && borrow != UINT64_C(0); ++i) {
    const uint64_t previous = result.limbs[i];
    result.limbs[i]--;
    borrow = previous == UINT64_C(0);
  }
  return result;
}

static inline u256 u256_sub_u128(const u256 lhs,
                                      const u128 rhs) {
  u256 result = lhs;
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
static inline u128 u128_sub_u256(const u128 lhs,
                                      const u256 rhs) {
  u128 result;
  result.limbs[0] = lhs.limbs[0] - rhs.limbs[0];
  const uint64_t borrow = lhs.limbs[0] < rhs.limbs[0];
  result.limbs[1] = lhs.limbs[1] - rhs.limbs[1] - borrow;
  return result;
}

/* The Sail range checker proves that rhs fits and rhs <= lhs at each emitted
 * u64 - u256 call site.  The helper only expresses the selected C
 * representation; it does not add a second runtime semantics. */
static inline uint64_t u64_sub_u256(const uint64_t lhs,
                                    const u256 rhs) {
  return lhs - rhs.limbs[0];
}

static inline u256 u256_mul_u64(const u256 lhs,
                                     const uint64_t rhs) {
  u256 result = {{0}};
  unsigned __int128 carry = 0;
  for (size_t i = 0; i < 4; ++i) {
    const unsigned __int128 product =
        ((unsigned __int128)lhs.limbs[i] * rhs) + carry;
    result.limbs[i] = (uint64_t)product;
    carry = product >> 64;
  }
  return result;
}

static inline u256 u256_mul_u128(const u256 lhs,
                                      const u128 rhs) {
  u256 result = {{0}};
  for (size_t i = 0; i < 4; ++i) {
    unsigned __int128 carry = 0;
    for (size_t j = 0; j < 2 && i + j < 4; ++j) {
      const size_t k = i + j;
      const unsigned __int128 sum =
          ((unsigned __int128)lhs.limbs[i] * rhs.limbs[j])
          + result.limbs[k] + carry;
      result.limbs[k] = (uint64_t)sum;
      carry = sum >> 64;
    }
    if (i + 2 < 4) {
      result.limbs[i + 2] = (uint64_t)carry;
    }
  }
  return result;
}

static inline u256 u256_div_u64(const u256 dividend,
                                     const uint64_t divisor) {
  u256 quotient = {{0}};
  uint64_t remainder = UINT64_C(0);
  for (size_t i = 4; i-- > 0;) {
    const unsigned __int128 partial =
        ((unsigned __int128)remainder << 64) | dividend.limbs[i];
    quotient.limbs[i] = (uint64_t)(partial / divisor);
    remainder = (uint64_t)(partial % divisor);
  }
  return quotient;
}

static inline u256 u256_mod_u64(const u256 dividend,
                                     const uint64_t divisor) {
  u256 result = {{0}};
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
  while (count != 0 && value[count - 1] == UINT64_C(0)) {
    count--;
  }
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

  if (quotient != NULL) {
    for (size_t i = 0; i < 8; ++i) {
      quotient[i] = UINT64_C(0);
    }
  }
  if (remainder != NULL) {
    for (size_t i = 0; i < 4; ++i) {
      remainder[i] = UINT64_C(0);
    }
  }
  if (un == 0) {
    return;
  }
  if (un < vn) {
    if (remainder != NULL) {
      for (size_t i = 0; i < un; ++i) {
        remainder[i] = numerator[i];
      }
    }
    return;
  }

  if (vn == 1) {
    uint64_t rem = UINT64_C(0);
    for (size_t i = un; i-- > 0;) {
      const unsigned __int128 partial =
          ((unsigned __int128)rem << 64) | numerator[i];
      if (quotient != NULL) {
        quotient[i] = (uint64_t)(partial / divisor[0]);
      }
      rem = (uint64_t)(partial % divisor[0]);
    }
    if (remainder != NULL) {
      remainder[0] = rem;
    }
    return;
  }

  const unsigned shift = u256_leading_zeros(divisor[vn - 1]);
  if (shift == 0) {
    for (size_t i = 0; i < vn; ++i) {
      v[i] = divisor[i];
    }
    for (size_t i = 0; i < un; ++i) {
      u[i] = numerator[i];
    }
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
          ((unsigned __int128)qhat * v[i]) + borrow;
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
    if (quotient != NULL) {
      quotient[j] = qhat;
    }
  }

  if (remainder != NULL) {
    if (shift == 0) {
      for (size_t i = 0; i < vn; ++i) {
        remainder[i] = u[i];
      }
    } else {
      for (size_t i = 0; i < vn; ++i) {
        remainder[i] = u[i] >> shift;
        if (i + 1 < vn) {
          remainder[i] |= u[i + 1] << (64 - shift);
        }
      }
    }
  }
}

static inline u256 u256_div_u128(const u256 dividend,
                                      const u128 divisor) {
  u256 result = {{0}};
  const uint64_t words[4] = {
      divisor.limbs[0], divisor.limbs[1], UINT64_C(0), UINT64_C(0)};
  uint64_t quotient[8] = {0};
  u256_divrem_words(dividend.limbs, 4, words, quotient, NULL);
  for (size_t i = 0; i < 4; ++i) {
    result.limbs[i] = quotient[i];
  }
  return result;
}

static inline u256 u256_mod_u128(const u256 dividend,
                                      const u128 divisor) {
  u256 result = {{0}};
  const uint64_t words[4] = {
      divisor.limbs[0], divisor.limbs[1], UINT64_C(0), UINT64_C(0)};
  u256_divrem_words(dividend.limbs, 4, words, NULL, result.limbs);
  return result;
}

static inline u128 u128_div_u256(const u128 dividend,
                                      const u256 divisor) {
  u128 result = {{0}};
  if ((divisor.limbs[2] | divisor.limbs[3]) != UINT64_C(0)) {
    return result;
  }
  uint64_t quotient[8] = {0};
  u256_divrem_words(dividend.limbs, 2, divisor.limbs, quotient, NULL);
  result.limbs[0] = quotient[0];
  result.limbs[1] = quotient[1];
  return result;
}

static inline u128 u128_mod_u256(const u128 dividend,
                                      const u256 divisor) {
  if ((divisor.limbs[2] | divisor.limbs[3]) != UINT64_C(0)) {
    return dividend;
  }
  uint64_t remainder[4] = {0};
  u256_divrem_words(dividend.limbs, 2, divisor.limbs, NULL, remainder);
  u128 result = {{remainder[0], remainder[1]}};
  return result;
}

static inline u256 u256_div(const u256 dividend,
                                 const u256 divisor) {
  u256 result = {{0}};
  uint64_t quotient[8] = {0};
  u256_divrem_words(dividend.limbs, 4, divisor.limbs, quotient, NULL);
  for (size_t i = 0; i < 4; ++i) {
    result.limbs[i] = quotient[i];
  }
  return result;
}

static inline u256 u256_mod(const u256 dividend,
                                 const u256 divisor) {
  u256 result = {{0}};
  u256_divrem_words(dividend.limbs, 4, divisor.limbs, NULL, result.limbs);
  return result;
}

static inline u256 u256_addmod(const u256 lhs,
                                    const u256 rhs,
                                    const u256 modulus) {
  u256 result = {{0}};
  uint64_t sum[5] = {0};
  uint64_t carry = UINT64_C(0);
  for (size_t i = 0; i < 4; ++i) {
    const unsigned __int128 wide =
        (unsigned __int128)lhs.limbs[i] + rhs.limbs[i] + carry;
    sum[i] = (uint64_t)wide;
    carry = (uint64_t)(wide >> 64);
  }
  sum[4] = carry;
  if (!u256_is_zero(modulus)) {
    u256_divrem_words(sum, 5, modulus.limbs, NULL, result.limbs);
  }
  return result;
}

static inline u256 u256_mulmod(const u256 lhs,
                                    const u256 rhs,
                                    const u256 modulus) {
  u256 result = {{0}};
  uint64_t product[8] = {0};
  for (size_t i = 0; i < 4; ++i) {
    uint64_t carry = UINT64_C(0);
    for (size_t j = 0; j < 4; ++j) {
      const size_t k = i + j;
      const unsigned __int128 wide =
          ((unsigned __int128)lhs.limbs[i] * rhs.limbs[j])
          + product[k] + carry;
      product[k] = (uint64_t)wide;
      carry = (uint64_t)(wide >> 64);
    }
    product[i + 4] = carry;
  }
  if (!u256_is_zero(modulus)) {
    u256_divrem_words(product, 8, modulus.limbs, NULL, result.limbs);
  }
  return result;
}

static inline u256 u256_shiftl_u64(const u256 value, const uint64_t amount) {
  u256 result = {{0}};
  if (amount >= UINT64_C(256)) {
    return result;
  }
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

static inline u256 u256_shiftr_u64(const u256 value, const uint64_t amount) {
  u256 result = {{0}};
  if (amount >= UINT64_C(256)) {
    return result;
  }
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

static inline u256 u256_arith_shiftr_u64(const u256 value, const uint64_t amount) {
  if ((value.limbs[3] >> 63) == 0) {
    return u256_shiftr_u64(value, amount);
  }
  return u256_not(u256_shiftr_u64(u256_not(value), amount));
}

static inline uint64_t u256_abs_i64(const int64_t amount) {
  return amount < 0 ? (uint64_t)(-(amount + 1)) + UINT64_C(1) : (uint64_t)amount;
}

static inline u256 u256_shiftl_i64(const u256 value, const int64_t amount) {
  return u256_shiftl_u64(value, u256_abs_i64(amount));
}

static inline u256 u256_shiftr_i64(const u256 value, const int64_t amount) {
  return u256_shiftr_u64(value, u256_abs_i64(amount));
}

static inline u256 u256_arith_shiftr_i64(const u256 value, const int64_t amount) {
  return u256_arith_shiftr_u64(value, u256_abs_i64(amount));
}

static inline u256 u256_of_fbits(const uint64_t value) {
  u256 result = {{0}};
  result.limbs[0] = value;
  return result;
}
|}
      in
      let string_helpers =
        string
          {|
static inline void string_of_u256(sail_string *result, const u256 value) {
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
static inline u256 u256_of_lbits(const lbits value) {
  u256 result = {{0}};
  sail_lbits_to_u64_array(result.limbs, 4, value);
  return result;
}

static inline void lbits_of_u256(lbits *result, const u256 value) {
  sail_lbits_from_u64_array(result, value.limbs, 4, UINT64_C(256));
}

static inline void decimal_string_of_u256(sail_string *result, const u256 value) {
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
static inline u256 undefined_u256(const sail_int len) {
  (void)len;
  return u256_zero();
}

static inline uint64_t vector_access_u256(const u256 value, const sail_int index) {
  return u256_bit(value, (int64_t)sail_int_get_ui(index));
}

static inline u256 u256_shiftl(const u256 value, const sail_int amount) {
  return u256_shiftl_u64(value, sail_int_get_ui(amount));
}

static inline u256 u256_shiftr(const u256 value, const sail_int amount) {
  return u256_shiftr_u64(value, sail_int_get_ui(amount));
}

static inline u256 u256_arith_shiftr(const u256 value, const sail_int amount) {
  return u256_arith_shiftr_u64(value, sail_int_get_ui(amount));
}

static inline void u256_unsigned(sail_int *result, const u256 value) {
  sail_int_from_u64_array(result, value.limbs, 4);
}

static inline void u128_unsigned(sail_int *result, const u128 value) {
  sail_int_from_u64_array(result, value.limbs, 2);
}

static inline void u256_signed(sail_int *result, const u256 value) {
  sail_int_from_twos_complement_u64_array(result, value.limbs, 4);
}

static inline u256 u256_of_sail_int(const sail_int value) {
  u256 result = {{0}};
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
typedef struct { uint64_t limbs[2]; } u128;
#endif

#ifndef SAIL_U256_DEFINED
#define SAIL_U256_DEFINED
typedef struct { uint64_t limbs[4]; } u256;
#endif

#ifndef SAIL_U320_DEFINED
#define SAIL_U320_DEFINED
typedef struct { uint64_t limbs[5]; } u320;
#endif
|}
      in
      let base_helpers =
        string
          {|
static inline u320 u320_zero(void) {
  u320 result = {{0}};
  return result;
}

static inline u320 u320_of_u64(const uint64_t value) {
  u320 result = {{value, UINT64_C(0), UINT64_C(0), UINT64_C(0), UINT64_C(0)}};
  return result;
}

static inline u320 u320_of_u128(const u128 value) {
  u320 result = {{
      value.limbs[0], value.limbs[1], UINT64_C(0), UINT64_C(0), UINT64_C(0)}};
  return result;
}

static inline u320 u320_of_u256(const u256 value) {
  u320 result = {{
      value.limbs[0], value.limbs[1], value.limbs[2], value.limbs[3],
      UINT64_C(0)}};
  return result;
}

static inline uint64_t u320_to_u64(const u320 value) {
  if ((value.limbs[1] | value.limbs[2] | value.limbs[3] | value.limbs[4])
      != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint64_t domain");
  }
  return value.limbs[0];
}

static inline u128 u128_of_u320(const u320 value) {
  if ((value.limbs[2] | value.limbs[3] | value.limbs[4]) != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint128_t domain");
  }
  u128 result = {{value.limbs[0], value.limbs[1]}};
  return result;
}

static inline u256 u256_of_u320(const u320 value) {
  if (value.limbs[4] != UINT64_C(0)) {
    sail_native_conversion_failure("integer value is outside the uint256_t domain");
  }
  u256 result = {{
      value.limbs[0], value.limbs[1], value.limbs[2], value.limbs[3]}};
  return result;
}

static inline bool eq_u320(const u320 lhs, const u320 rhs) {
  for (size_t i = 0; i < 5; ++i) {
    if (lhs.limbs[i] != rhs.limbs[i]) {
      return false;
    }
  }
  return true;
}

static inline bool u320_lt(const u320 lhs, const u320 rhs) {
  for (size_t i = 5; i-- > 0;) {
    if (lhs.limbs[i] != rhs.limbs[i]) {
      return lhs.limbs[i] < rhs.limbs[i];
    }
  }
  return false;
}

static inline u320 u320_add(const u320 lhs, const u320 rhs) {
  u320 result = {0};
  uint64_t carry = UINT64_C(0);
  for (size_t i = 0; i < 5; ++i) {
    const unsigned __int128 sum =
        (unsigned __int128)lhs.limbs[i] + rhs.limbs[i] + carry;
    result.limbs[i] = (uint64_t)sum;
    carry = (uint64_t)(sum >> 64);
  }
  return result;
}

static inline u320 u320_sub(const u320 lhs, const u320 rhs) {
  u320 result = {0};
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

static inline u320 u320_mul(const u320 lhs, const u320 rhs) {
  u320 result = {{0}};
  for (size_t i = 0; i < 5; ++i) {
    unsigned __int128 carry = 0;
    for (size_t j = 0; i + j < 5; ++j) {
      const size_t k = i + j;
      const unsigned __int128 sum =
          ((unsigned __int128)lhs.limbs[i] * rhs.limbs[j])
          + result.limbs[k] + carry;
      result.limbs[k] = (uint64_t)sum;
      carry = sum >> 64;
    }
  }
  return result;
}

static inline u320 u320_identity(const u320 value) {
  return value;
}

static inline u320 u320_add_scalar(
    const u320 lhs, const uint64_t rhs) {
  u320 result = lhs;
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

static inline u320 u320_mul_scalar(
    const u320 lhs, const uint64_t rhs) {
  u320 result = {0};
  unsigned __int128 carry = 0;
  for (size_t i = 0; i < 5; ++i) {
    const unsigned __int128 product =
        ((unsigned __int128)lhs.limbs[i] * rhs) + carry;
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
      u320: stem##_u320, \
      u256: stem##_u256, \
      u128: stem##_u128, \
      default: stem##_u64)

#define U320_SELECT_BINARY(operation, lhs, rhs) \
  _Generic((lhs), \
      u320: U320_SELECT_RHS(u320_##operation##_u320, rhs), \
      u256: U320_SELECT_RHS(u320_##operation##_u256, rhs), \
      u128: U320_SELECT_RHS(u320_##operation##_u128, rhs), \
      default: U320_SELECT_RHS(u320_##operation##_u64, rhs))

#define u320_add_widen(lhs, rhs) \
  U320_SELECT_BINARY(add, lhs, rhs)((lhs), (rhs))

#define u320_mul_widen(lhs, rhs) \
  U320_SELECT_BINARY(mul, lhs, rhs)((lhs), (rhs))

static inline u320 u320_add_u320_u320(
    const u320 lhs, const u320 rhs) {
  return u320_add(lhs, rhs);
}

static inline u320 u320_add_u320_u256(
    const u320 lhs, const u256 rhs) {
  return u320_add(lhs, u320_of_u256(rhs));
}

static inline u320 u320_add_u320_u128(
    const u320 lhs, const u128 rhs) {
  return u320_add(lhs, u320_of_u128(rhs));
}

static inline u320 u320_add_u320_u64(
    const u320 lhs, const uint64_t rhs) {
  return u320_add_scalar(lhs, rhs);
}

static inline u320 u320_add_u256_u320(
    const u256 lhs, const u320 rhs) {
  return u320_add(rhs, u320_of_u256(lhs));
}

static inline u320 u320_add_u256_u256(
    const u256 lhs, const u256 rhs) {
  return u320_add(u320_of_u256(lhs), u320_of_u256(rhs));
}

static inline u320 u320_add_u256_u128(
    const u256 lhs, const u128 rhs) {
  return u320_add(u320_of_u256(lhs), u320_of_u128(rhs));
}

static inline u320 u320_add_u128_u256(
    const u128 lhs, const u256 rhs) {
  return u320_add_u256_u128(rhs, lhs);
}

static inline u320 u320_add_u256_u64(
    const u256 lhs, const uint64_t rhs) {
  return u320_add_scalar(u320_of_u256(lhs), rhs);
}

static inline u320 u320_add_u64_u256(
    const uint64_t lhs, const u256 rhs) {
  return u320_add_u256_u64(rhs, lhs);
}

static inline u320 u320_add_u128_u128(
    const u128 lhs, const u128 rhs) {
  return u320_add(u320_of_u128(lhs), u320_of_u128(rhs));
}

static inline u320 u320_add_u128_u320(
    const u128 lhs, const u320 rhs) {
  return u320_add(rhs, u320_of_u128(lhs));
}

static inline u320 u320_add_u128_u64(
    const u128 lhs, const uint64_t rhs) {
  return u320_add_scalar(u320_of_u128(lhs), rhs);
}

static inline u320 u320_add_u64_u128(
    const uint64_t lhs, const u128 rhs) {
  return u320_add_u128_u64(rhs, lhs);
}

static inline u320 u320_add_u64_u64(
    const uint64_t lhs, const uint64_t rhs) {
  return u320_add_scalar(u320_of_u64(lhs), rhs);
}

static inline u320 u320_add_u64_u320(
    const uint64_t lhs, const u320 rhs) {
  return u320_add_scalar(rhs, lhs);
}

static inline u320 u320_mul_u320_u320(
    const u320 lhs, const u320 rhs) {
  return u320_mul(lhs, rhs);
}

static inline u320 u320_mul_u320_u256(
    const u320 lhs, const u256 rhs) {
  return u320_mul(lhs, u320_of_u256(rhs));
}

static inline u320 u320_mul_u320_u128(
    const u320 lhs, const u128 rhs) {
  return u320_mul(lhs, u320_of_u128(rhs));
}

static inline u320 u320_mul_u320_u64(
    const u320 lhs, const uint64_t rhs) {
  return u320_mul_scalar(lhs, rhs);
}

static inline u320 u320_mul_u256_u320(
    const u256 lhs, const u320 rhs) {
  return u320_mul(rhs, u320_of_u256(lhs));
}

static inline u320 u320_mul_u256_u256(
    const u256 lhs, const u256 rhs) {
  return u320_mul(u320_of_u256(lhs), u320_of_u256(rhs));
}

static inline u320 u320_mul_u256_u128(
    const u256 lhs, const u128 rhs) {
  return u320_mul(u320_of_u256(lhs), u320_of_u128(rhs));
}

static inline u320 u320_mul_u128_u256(
    const u128 lhs, const u256 rhs) {
  return u320_mul_u256_u128(rhs, lhs);
}

static inline u320 u320_mul_u256_u64(
    const u256 lhs, const uint64_t rhs) {
  return u320_mul_scalar(u320_of_u256(lhs), rhs);
}

static inline u320 u320_mul_u64_u256(
    const uint64_t lhs, const u256 rhs) {
  return u320_mul_u256_u64(rhs, lhs);
}

static inline u320 u320_mul_u128_u128(
    const u128 lhs, const u128 rhs) {
  return u320_mul(u320_of_u128(lhs), u320_of_u128(rhs));
}

static inline u320 u320_mul_u128_u320(
    const u128 lhs, const u320 rhs) {
  return u320_mul(rhs, u320_of_u128(lhs));
}

static inline u320 u320_mul_u128_u64(
    const u128 lhs, const uint64_t rhs) {
  return u320_mul_scalar(u320_of_u128(lhs), rhs);
}

static inline u320 u320_mul_u64_u128(
    const uint64_t lhs, const u128 rhs) {
  return u320_mul_u128_u64(rhs, lhs);
}

static inline u320 u320_mul_u64_u64(
    const uint64_t lhs, const uint64_t rhs) {
  return u320_mul_scalar(u320_of_u64(lhs), rhs);
}

static inline u320 u320_mul_u64_u320(
    const uint64_t lhs, const u320 rhs) {
  return u320_mul_scalar(rhs, lhs);
}

static inline u256 u256_sub_u320(
    const u256 lhs, const u320 rhs) {
  return u256_of_u320(u320_sub(u320_of_u256(lhs), rhs));
}

static inline u128 u128_sub_u320(
    const u128 lhs, const u320 rhs) {
  return u128_of_u320(u320_sub(u320_of_u128(lhs), rhs));
}

static inline uint64_t u64_sub_u320(
    const uint64_t lhs, const u320 rhs) {
  return u320_to_u64(u320_sub(u320_of_u64(lhs), rhs));
}

/* Base-2^64 long division for the common five-by-one-limb shape. */
static inline void u320_divrem_u64(
    const u320 dividend,
    const uint64_t divisor,
    u320 *quotient,
    uint64_t *remainder) {
  u320 q = {{0}};
  uint64_t rem = UINT64_C(0);
  for (size_t i = 5; i-- > 0;) {
    const unsigned __int128 partial =
        ((unsigned __int128)rem << 64) | dividend.limbs[i];
    q.limbs[i] = (uint64_t)(partial / divisor);
    rem = (uint64_t)(partial % divisor);
  }
  if (quotient != NULL) {
    *quotient = q;
  }
  if (remainder != NULL) {
    *remainder = rem;
  }
}

static inline u320 u320_div_u64(
    const u320 dividend, const uint64_t divisor) {
  u320 result;
  u320_divrem_u64(dividend, divisor, &result, NULL);
  return result;
}

static inline uint64_t u320_mod_u64(
    const u320 dividend, const uint64_t divisor) {
  uint64_t result;
  u320_divrem_u64(dividend, divisor, NULL, &result);
  return result;
}

static inline bool u320_is_zero(const u320 value) {
  return (value.limbs[0] | value.limbs[1] | value.limbs[2]
          | value.limbs[3] | value.limbs[4]) == UINT64_C(0);
}

static inline bool u320_power_of_two_shift(
    const u320 value, uint32_t *shift) {
  uint32_t found = UINT32_MAX;
  for (uint32_t i = 0; i < 5; ++i) {
    const uint64_t limb = value.limbs[i];
    if (limb == UINT64_C(0)) {
      continue;
    }
    if ((limb & (limb - UINT64_C(1))) != UINT64_C(0) || found != UINT32_MAX) {
      return false;
    }
    found = (i * 64U) + (uint32_t)__builtin_ctzll(limb);
  }
  if (found == UINT32_MAX) {
    return false;
  }
  *shift = found;
  return true;
}

static inline u320 u320_shr(const u320 value, const uint32_t shift) {
  u320 result = {{0}};
  if (shift >= 320U) {
    return result;
  }
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

static inline u320 u320_mod_power_of_two(
    const u320 value, const uint32_t shift) {
  if (shift >= 320U) {
    return value;
  }
  u320 result = value;
  const uint32_t word = shift / 64U;
  const uint32_t bits = shift % 64U;
  if (bits == 0U) {
    for (uint32_t i = word; i < 5U; ++i) {
      result.limbs[i] = UINT64_C(0);
    }
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
    const u320 dividend,
    const u320 divisor,
    u320 *quotient,
    u320 *remainder) {
  if (u320_is_zero(divisor)) {
    sail_native_conversion_failure("division by zero");
  }
  if ((divisor.limbs[1] | divisor.limbs[2]
       | divisor.limbs[3] | divisor.limbs[4]) == UINT64_C(0)) {
    u320 q;
    uint64_t r;
    u320_divrem_u64(dividend, divisor.limbs[0], &q, &r);
    if (quotient != NULL) {
      *quotient = q;
    }
    if (remainder != NULL) {
      *remainder = u320_of_u64(r);
    }
    return;
  }
  uint32_t shift;
  if (u320_power_of_two_shift(divisor, &shift)) {
    if (quotient != NULL) {
      *quotient = u320_shr(dividend, shift);
    }
    if (remainder != NULL) {
      *remainder = u320_mod_power_of_two(dividend, shift);
    }
    return;
  }

  u320 q = {{0}};
  u320 rem = {{0}};
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
  if (quotient != NULL) {
    *quotient = q;
  }
  if (remainder != NULL) {
    *remainder = rem;
  }
}

static inline u320 u320_div(
    const u320 dividend, const u320 divisor) {
  u320 result;
  u320_divrem(dividend, divisor, &result, NULL);
  return result;
}

static inline u320 u320_mod(
    const u320 dividend, const u320 divisor) {
  u320 result;
  u320_divrem(dividend, divisor, NULL, &result);
  return result;
}
|}
      in
      let generic_sail_int_helpers =
        string
          {|
static inline u320 u320_of_sail_int(const sail_int value) {
  u320 result = {{0}};
  sail_int_to_u64_array(result.limbs, 5, value);
  return result;
}

static inline void u320_unsigned(sail_int *result, const u320 value) {
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
      let ctyp = fixed_bytes_type_name (c_repr_fixed_bytes_ctyp length) in
      let type_name = ctyp in
      let guard = sprintf "SAIL_FIXED_BYTES_%d_DEFINED" length in
      let typedef =
        ksprintf string "#ifndef %s\n#define %s\ntypedef struct { uint8_t bytes[%d]; } %s;\n#endif" guard guard length
          ctyp
      in
      let zero_helper =
        ksprintf string {|
static inline %s %s_zero(void) {
  %s result = {{0}};
  return result;
}
|} ctyp type_name
          ctyp
      in
      let equality_helper =
        if length = 20 then
          ksprintf string
            {|

static inline bool eq_%s(const %s op1, const %s op2) {
  if (memcmp(op1.bytes, op2.bytes, 8) != 0) {
    return false;
  }
  if (memcmp(op1.bytes + 8, op2.bytes + 8, 8) != 0) {
    return false;
  }
  return memcmp(op1.bytes + 16, op2.bytes + 16, 4) == 0;
}
|}
            type_name ctyp ctyp
        else
          ksprintf string
            {|

static inline bool eq_%s(const %s op1, const %s op2) {
  return memcmp(op1.bytes, op2.bytes, %d) == 0;
}
|}
            type_name ctyp ctyp length
      in
      let base_helpers = zero_helper ^^ equality_helper in
      let byte_u256_helpers =
        if length > 32 then empty
        else
          ksprintf string
            {|

#ifndef SAIL_U256_DEFINED
#define SAIL_U256_DEFINED
typedef struct { uint64_t limbs[4]; } u256;
#endif

static inline u256 u256_from_%s(const %s value) {
  u256 result = {{0}};
  for (size_t i = 0; i < %d; ++i) {
    result.limbs[i >> 3] |= ((uint64_t)value.bytes[i]) << ((i & 7) * 8);
  }
  return result;
}

static inline %s %s_from_u256(const u256 value) {
  %s result = {0};
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
  %s result = {0};
  for (size_t i = 0; i < %d; ++i) {
    result.bytes[i] = (uint8_t)elem;
  }
  return result;
}

static inline %s undefined_vector_%s(const sail_int length_arg, const uint64_t elem) {
  return vector_init_%s(length_arg, elem);
}

static inline %s vector_update_%s(%s value, const sail_int index, const uint64_t elem) {
  const uint64_t i = sail_int_get_ui(index);
  if (i < %d) {
    value.bytes[i] = (uint8_t)elem;
  }
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
  if (index >= 0 && index < %d) {
    value.bytes[index] = (uint8_t)elem;
  }
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
  if (index < %d) {
    value.bytes[index] = (uint8_t)elem;
  }
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
  %s result = {0};
  for (size_t i = 0; i < %d; ++i) {
    result.bytes[i] = (uint8_t)elem;
  }
  return result;
}

static inline %s fast_unsigned_vector_init_%s(const uint64_t length_arg, const uint64_t elem) {
  (void)length_arg;
  %s result = {0};
  for (size_t i = 0; i < %d; ++i) {
    result.bytes[i] = (uint8_t)elem;
  }
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

  let codegen_fixed_bytes_u64_lanes length =
    let id = mk_id ("__sail_c_repr_fixed_bytes_u64_lanes_" ^ string_of_int length) in
    if IdSet.mem id !generated then []
    else (
      generated := IdSet.add id !generated;
      let lane_count = (length + 7) / 8 in
      let tail_bytes = length mod 8 in
      let tail_mask = if tail_bytes = 0 then "UINT64_MAX" else sprintf "(UINT64_MAX >> %d)" (64 - (tail_bytes * 8)) in
      let ctyp = fixed_bytes_type_name (c_repr_fixed_bytes_u64_lanes_ctyp length) in
      let type_name = ctyp in
      let guard = sprintf "SAIL_FIXED_BYTES_U64_LANES_%d_DEFINED" length in
      let typedef =
        ksprintf string "#ifndef %s\n#define %s\ntypedef struct { uint64_t lanes[%d]; } %s;\n#endif" guard guard
          lane_count ctyp
      in
      let base_helpers =
        ksprintf string
          {|
static inline %s %s_zero(void) {
  %s result = {{0}};
  return result;
}

static inline bool eq_%s(const %s op1, const %s op2) {
  for (size_t i = 0; i < %d; ++i) {
    if (op1.lanes[i] != op2.lanes[i]) {
      return false;
    }
  }
  return true;
}
|}
          ctyp type_name ctyp type_name ctyp ctyp lane_count
      in
      let byte_u256_helpers =
        if length > 32 then empty
        else
          ksprintf string
            {|

#ifndef SAIL_U256_DEFINED
#define SAIL_U256_DEFINED
typedef struct { uint64_t limbs[4]; } u256;
#endif

static inline u256 u256_from_%s(const %s value) {
  u256 result = {{0}};
  for (size_t i = 0; i < %d; ++i) {
    result.limbs[i] = value.lanes[i];
  }
  result.limbs[%d] &= %s;
  return result;
}

static inline %s %s_from_u256(const u256 value) {
  %s result = {{0}};
  for (size_t i = 0; i < %d; ++i) {
    result.lanes[i] = value.limbs[i];
  }
  result.lanes[%d] &= %s;
  return result;
}
|}
            type_name ctyp lane_count (lane_count - 1) tail_mask ctyp type_name ctyp lane_count (lane_count - 1)
            tail_mask
      in
      let generic_helpers =
        ksprintf string
          {|

static inline %s vector_init_%s(const sail_int length_arg, const uint64_t elem) {
  (void)length_arg;
  %s result = {0};
  const uint64_t fill = UINT64_C(0x0101010101010101) * (uint8_t)elem;
  for (size_t i = 0; i < %d; ++i) {
    result.lanes[i] = fill;
  }
  result.lanes[%d] &= %s;
  return result;
}

static inline %s undefined_vector_%s(const sail_int length_arg, const uint64_t elem) {
  return vector_init_%s(length_arg, elem);
}

static inline %s vector_update_%s(%s value, const sail_int index, const uint64_t elem) {
  const uint64_t i = sail_int_get_ui(index);
  if (i < %d) {
    const uint64_t shift = (i & UINT64_C(7)) * UINT64_C(8);
    const uint64_t mask = UINT64_C(0xff) << shift;
    value.lanes[i >> 3] = (value.lanes[i >> 3] & ~mask) | (((uint64_t)(uint8_t)elem) << shift);
  }
  return value;
}

static inline uint64_t vector_access_%s(const %s value, const sail_int index) {
  const uint64_t i = sail_int_get_ui(index);
  return i < %d ? ((value.lanes[i >> 3] >> ((i & UINT64_C(7)) * UINT64_C(8))) & UINT64_C(0xff))
                : UINT64_C(0);
}

static inline void length_%s(sail_int *result, const %s value) {
  (void)value;
  mpz_set_ui(*result, %d);
}
|}
          ctyp type_name ctyp lane_count (lane_count - 1) tail_mask ctyp type_name type_name ctyp type_name ctyp length
          type_name ctyp length type_name ctyp length
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
  if (index >= 0 && index < %d) {
    const uint64_t i = (uint64_t)index;
    const uint64_t shift = (i & UINT64_C(7)) * UINT64_C(8);
    const uint64_t mask = UINT64_C(0xff) << shift;
    value.lanes[i >> 3] = (value.lanes[i >> 3] & ~mask) | (((uint64_t)(uint8_t)elem) << shift);
  }
  return value;
}

static inline uint64_t fast_vector_access_%s(const %s value, const int64_t index) {
  if (index < 0 || index >= %d) {
    return UINT64_C(0);
  }
  const uint64_t i = (uint64_t)index;
  return (value.lanes[i >> 3] >> ((i & UINT64_C(7)) * UINT64_C(8))) & UINT64_C(0xff);
}
|}
          ctyp type_name type_name ctyp type_name ctyp length type_name ctyp length
      in
      let native_unsigned_index_helpers =
        ksprintf string
          {|
static inline %s fast_unsigned_vector_update_%s(
    %s value, const uint64_t index, const uint64_t elem) {
  if (index < %d) {
    const uint64_t shift = (index & UINT64_C(7)) * UINT64_C(8);
    const uint64_t mask = UINT64_C(0xff) << shift;
    value.lanes[index >> 3] =
        (value.lanes[index >> 3] & ~mask) | (((uint64_t)(uint8_t)elem) << shift);
  }
  return value;
}

static inline uint64_t fast_unsigned_vector_access_%s(
    const %s value, const uint64_t index) {
  return index < %d
             ? ((value.lanes[index >> 3] >> ((index & UINT64_C(7)) * UINT64_C(8))) & UINT64_C(0xff))
             : UINT64_C(0);
}
|}
          ctyp type_name ctyp length type_name ctyp length
      in
      let native_init_helpers =
        ksprintf string
          {|
static inline %s fast_vector_init_%s(const int64_t length_arg, const uint64_t elem) {
  (void)length_arg;
  %s result = {0};
  const uint64_t fill = UINT64_C(0x0101010101010101) * (uint8_t)elem;
  for (size_t i = 0; i < %d; ++i) {
    result.lanes[i] = fill;
  }
  result.lanes[%d] &= %s;
  return result;
}

static inline %s fast_unsigned_vector_init_%s(const uint64_t length_arg, const uint64_t elem) {
  (void)length_arg;
  return fast_vector_init_%s((int64_t)length_arg, elem);
}
|}
          ctyp type_name ctyp lane_count (lane_count - 1) tail_mask ctyp type_name type_name
      in
      let helpers =
        base_helpers ^^ byte_u256_helpers
        ^^ (if !emit_generic_sail_int_helpers then generic_helpers else empty)
        ^^ native_signed_index_helpers ^^ native_unsigned_index_helpers ^^ native_init_helpers
      in
      [TypeDeclaration typedef; StaticFunctionDefinition helpers]
    )

  let codegen_tup ctx ctyps =
    let tuple_ctyp = CT_tup ctyps in
    let key = mk_id ("tuple_" ^ string_of_ctyp tuple_ctyp) in
    let id = if Config.no_mangle then mk_id (readable_ctyp_name tuple_ctyp) else key in
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
        ^^ hardline
        ^^ string "  if (*rop == NULL) {\n    return;\n  }\n"
        ^^ string "  if ((*rop)->rc >= 1) {\n" ^^ string "    (*rop)->rc -= 1;\n" ^^ string "  }\n"
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
        ^^ string "  if (l == NULL) {\n    return;\n  }\n"
        ^^ string "  l->rc += 1;\n" ^^ string "}"
      in

      let codegen_dec_reference_count =
        string (sprintf "static void internal_dec_%s(%s l) {\n" (sgen_id id) (sgen_id id))
        ^^ string "  if (l == NULL) {\n    return;\n  }\n"
        ^^ string "  l->rc -= 1;\n" ^^ string "}"
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
        ^^ ksprintf string "  if (!same) {\n    internal_inc_%s(xs);\n  }\n" (sgen_id id)
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
      let stack_vector = is_stack_ctyp ctx vector_ctyp in
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
          [
            c_for
              (ksprintf string "(size_t i = 0; i < %d; ++i)" length)
              [sail_create ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[i]"];
          ]
      in
      let clear_elements =
        if stack_elem then []
        else
          [
            c_for
              (ksprintf string "(size_t i = 0; i < %d; ++i)" length)
              [sail_kill ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[i]"];
          ]
      in
      let create =
        c_function ~return:(static_type_helper_return "void") (sail_create name "%s *rop" name)
          ([ksprintf c_stmt "rop->len = %d" length] @ initialize_elements)
      in
      let clear =
        c_function ~return:(static_type_helper_return "void") (sail_kill name "%s *rop" name) clear_elements
      in
      let recreate =
        c_function ~return:(static_type_helper_return "void") (sail_recreate name "%s *rop" name)
          [sail_kill ~suffix:";" name "rop"; sail_create ~suffix:";" name "rop"]
      in
      let copy =
        c_function ~return:(static_type_helper_return "void")
          (sail_copy name "%s *rop, const %s op" name name)
          ( if stack_elem then [c_stmt "*rop = op"]
            else
              [
                c_stmt "rop->len = op.len";
                c_for
                  (ksprintf string "(size_t i = 0; i < %d; ++i)" length)
                  [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[i], op.data[i]"];
              ]
          )
      in
      let init name_suffix length_type length_expr =
        if stack_vector then
          c_function ~return:(static_type_helper_return name)
            (ksprintf string "%s_%s(const %s n, %s elem)" name_suffix name length_type (sgen_ctyp ctyp))
            [
              ksprintf c_stmt "%s vec" name;
              c_stmt ("size_t m = (size_t)" ^ length_expr);
              c_stmt "vec.len = m";
              c_for (string "(size_t i = 0; i < m; ++i)") [c_stmt "vec.data[i] = elem"];
              c_stmt "return vec";
            ]
        else
          c_function ~return:(static_type_helper_return "void")
            (ksprintf string "%s_%s(%s *vec, const %s n, %s elem)" name_suffix name name length_type (sgen_ctyp ctyp))
            [
              c_stmt ("size_t m = (size_t)" ^ length_expr);
              c_stmt "vec->len = m";
              c_for (string "(size_t i = 0; i < m; ++i)") [fill "i" "elem"];
            ]
      in
      let vector_init =
        c_function ~return:(static_type_helper_return "void")
          (ksprintf string "vector_init_%s(%s *vec, sail_int n, %s elem)" name name (sgen_ctyp ctyp))
          [
            c_stmt "size_t m = (size_t)sail_int_get_ui(n)";
            c_stmt "vec->len = m";
            c_for (string "(size_t i = 0; i < m; ++i)") [fill "i" "elem"];
          ]
      in
      let update function_name index_type index_expr =
        if stack_vector then
          c_function ~return:(static_type_helper_return name)
            (ksprintf string "%s_%s(%s op, const %s n, %s elem)" function_name name name index_type (sgen_ctyp ctyp))
            [c_stmt ("size_t m = (size_t)" ^ index_expr); c_stmt "op.data[m] = elem"; c_stmt "return op"]
        else
          c_function ~return:(static_type_helper_return "void")
            (ksprintf string "%s_%s(%s *rop, %s op, const %s n, %s elem)" function_name name name name index_type
               (sgen_ctyp ctyp)
            )
            [
              sail_copy ~suffix:";" name "rop, op";
              c_stmt ("size_t m = (size_t)" ^ index_expr);
              ( if stack_elem then c_stmt "rop->data[m] = elem"
                else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[m], elem"
              );
            ]
      in
      let vector_update =
        c_function ~return:(static_type_helper_return "void")
          (ksprintf string "vector_update_%s(%s *rop, %s op, sail_int n, %s elem)" name name name (sgen_ctyp ctyp))
          ([
             (if stack_elem then c_stmt "*rop = op" else sail_copy ~suffix:";" name "rop, op");
             c_stmt "size_t m = (size_t)sail_int_get_ui(n)";
           ]
          @ [
              ( if stack_elem then c_stmt "rop->data[m] = elem"
                else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[m], elem"
              );
            ]
          )
      in
      let access function_name index_type =
        if stack_elem then
          c_function
            ~return:(static_type_helper_return (sgen_ctyp ctyp))
            (ksprintf string "%s_%s(%s op, %s n)" function_name name name index_type)
            [c_stmt "return op.data[(size_t)n]"]
        else
          c_function ~return:(static_type_helper_return "void")
            (ksprintf string "%s_%s(%s *rop, %s op, %s n)" function_name name (sgen_ctyp ctyp) name index_type)
            [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "rop, op.data[(size_t)n]"]
      in
      let vector_access =
        if stack_elem then
          c_function
            ~return:(static_type_helper_return (sgen_ctyp ctyp))
            (ksprintf string "vector_access_%s(%s op, sail_int n)" name name)
            [c_stmt "return op.data[(size_t)sail_int_get_ui(n)]"]
        else
          c_function ~return:(static_type_helper_return "void")
            (ksprintf string "vector_access_%s(%s *rop, %s op, sail_int n)" name (sgen_ctyp ctyp) name)
            [sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "rop, op.data[(size_t)sail_int_get_ui(n)]"]
      in
      let internal_init =
        if stack_vector then
          c_function ~return:(static_type_helper_return name)
            (ksprintf string "internal_vector_init_%s(const int64_t len)" name)
            [ksprintf c_stmt "%s rop" name; c_stmt "rop.len = (size_t)len"; c_stmt "return rop"]
        else
          c_function ~return:(static_type_helper_return "void")
            (ksprintf string "internal_vector_init_%s(%s *rop, const int64_t len)" name name)
            [c_stmt "rop->len = (size_t)len"]
      in
      let internal_update = update "internal_vector_update" "int64_t" "n" in
      let equal =
        c_function ~return:(static_type_helper_return "bool")
          (sail_equal name "const %s op1, const %s op2" name name)
          [
            c_if (string "(op1.len != op2.len)") [c_stmt "return false"];
            c_stmt "bool result = true";
            c_for
              (string "(size_t i = 0; i < op1.len; ++i)")
              [c_assign (string "result") "&=" (codegen_equal ctyp "op1.data[i]" "op2.data[i]")];
            c_stmt "return result";
          ]
      in
      let undefined =
        c_function ~return:(static_type_helper_return "void")
          (ksprintf string "undefined_vector_%s(%s *rop, sail_int len, %s elem)" name name (sgen_ctyp ctyp))
          [
            c_stmt "size_t m = (size_t)sail_int_get_ui(len)";
            c_stmt "rop->len = m";
            c_for (string "(size_t i = 0; i < m; ++i)")
              [
                ( if stack_elem then c_stmt "rop->data[i] = elem"
                  else sail_copy ~suffix:";" (sgen_ctyp_name ctyp) "&rop->data[i], elem"
                );
              ];
          ]
      in
      let vector_length =
        c_function ~return:(static_type_helper_return "void")
          (ksprintf string "length_%s(sail_int *rop, %s op)" name name)
          [c_stmt "mpz_set_ui(*rop, (unsigned long int)op.len)"]
      in
      let static_helper helper_name doc =
        if Config.optimized_model && stack_vector then DemandedStaticFunctionDefinition (helper_name, doc)
        else StaticFunctionDefinition doc
      in
      generated := IdSet.add key !generated;
      [TypeDeclaration typedef]
      @ (if stack_vector then [] else List.map (fun d -> StaticFunctionDefinition d) [create; clear; recreate; copy])
      @ ( if !emit_generic_sail_int_helpers then
            List.map
              (fun d -> StaticFunctionDefinition d)
              [vector_init; vector_access; vector_update; undefined; vector_length]
          else []
        )
      @ [
          static_helper ("fast_vector_init_" ^ name) (init "fast_vector_init" "int64_t" "n");
          static_helper ("fast_unsigned_vector_init_" ^ name) (init "fast_unsigned_vector_init" "uint64_t" "n");
          static_helper ("fast_vector_access_" ^ name) (access "fast_vector_access" "int64_t");
          static_helper ("fast_unsigned_vector_access_" ^ name) (access "fast_unsigned_vector_access" "uint64_t");
          static_helper ("fast_vector_update_" ^ name) (update "fast_vector_update" "int64_t" "n");
          static_helper ("fast_unsigned_vector_update_" ^ name) (update "fast_unsigned_vector_update" "uint64_t" "n");
          static_helper ("eq_" ^ name) equal;
          static_helper ("internal_vector_update_" ^ name) internal_update;
          static_helper ("internal_vector_init_" ^ name) internal_init;
        ]
    )

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
          @ [c_if (string "(rop->data != NULL)") [c_stmt "sail_free(rop->data)"]]
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
            c_if (string "(op1.len != op2.len)") [c_stmt "return false"];
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
  (* A pure top-level Sail [let] whose initializer reduces to C constant
     expressions needs neither writable storage nor a runtime create/kill pair.
     The typed AST supplies declared [$[c_repr]] types before lowering; this
     final-JIB evaluator then uses the represented C type and exact lowered
     initializer.  Scalars, scalar aliases, fully-defined fixed vectors, and
     zero-initialized fixed-byte values are supported.  Other computed or
     managed values deliberately remain runtime initialized. *)
  type static_let_value = Static_scalar of vl | Static_vector of vl array

  type static_let_initializer = id * ctyp * static_let_value

  (* This cache is prepared from the complete final JIB program before C is
     emitted.  Looking at one letbind in isolation misses aliases such as
     [let SYSTEM_CALL_INPUT_LENGTH = WORD_BYTE_LENGTH]: C's file-scope
     constant-expression rules do not permit the generated const object to be
     used as an initializer, so the alias must inherit the original literal. *)
  let static_letbinds : (int * static_let_initializer list) list ref = ref []

  let static_letbind number = List.assoc_opt number !static_letbinds

  let static_letbind_initializers ?(known_globals = NameMap.empty) ctx bindings instrs =
    let static_literal = function
      | VL_bits _ | VL_int _ | VL_bool _ | VL_unit | VL_enum _ -> true
      | VL_real _ | VL_string _ | VL_ref _ | VL_undefined -> false
    in
    if (not Config.optimized_model) || not (List.for_all (fun (_, ctyp) -> is_stack_ctyp ctx ctyp) bindings) then None
    else (
      let binding_names = List.fold_left (fun names (id, _) -> NameSet.add (name id) names) NameSet.empty bindings in
      let locals = ref NameMap.empty in
      let globals = ref NameMap.empty in
      let valid = ref true in
      let rec resolve = function
        | V_lit (literal, _) when static_literal literal -> Some (Static_scalar literal)
        | V_id (source, _) -> (
            match NameMap.find_opt source !locals with
            | Some value -> Some value
            | None -> NameMap.find_opt source known_globals
          )
        | V_call ((Unsigned _ | Signed _ | Zero_extend _ | Sign_extend _), [value]) -> (
            match resolve value with Some (Static_scalar _ as value) -> Some value | _ -> None
          )
        | _ -> None
      in
      let convert destination_ctyp = function
        | Static_scalar literal -> Some (Static_scalar literal)
        | Static_vector elements as value -> (
            match destination_ctyp with
            | CT_fvector (length, _) when length = Array.length elements -> Some value
            | ctyp when is_c_repr_fixed_bytes ctyp -> (
                match c_repr_fixed_bytes_length ctyp with
                | Some length when length = Array.length elements -> Some value
                | _ -> None
              )
            | _ -> None
          )
      in
      let assign destination destination_ctyp value =
        match Option.bind (resolve value) (convert destination_ctyp) with
        | None -> valid := false
        | Some value when NameSet.mem destination binding_names ->
            if NameMap.mem destination !globals then valid := false
            else globals := NameMap.add destination value !globals
        | Some value -> locals := NameMap.add destination value !locals
      in
      let bit_literal_integer bits =
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
      in
      let scalar_integer = function
        | V_lit (VL_int value, _) -> Some value
        | V_lit (VL_bits bits, _) -> bit_literal_integer bits
        | value -> (
            match resolve value with
            | Some (Static_scalar (VL_int value)) -> Some value
            | Some (Static_scalar (VL_bits bits)) -> bit_literal_integer bits
            | _ -> None
          )
      in
      let vector_init destination destination_ctyp args =
        let destination_length =
          match destination_ctyp with
          | CT_fvector (length, _) -> Some length
          | ctyp when is_c_repr_fixed_bytes ctyp -> c_repr_fixed_bytes_length ctyp
          | _ -> None
        in
        match (destination_length, args) with
        | Some length, [requested_length] -> (
            match scalar_integer requested_length with
            | Some requested_length when Big_int.equal requested_length (Big_int.of_int length) ->
                let initial_element =
                  if is_c_repr_fixed_bytes destination_ctyp then VL_int Big_int.zero else VL_undefined
                in
                locals := NameMap.add destination (Static_vector (Array.make length initial_element)) !locals
            | _ -> valid := false
          )
        | _ -> valid := false
      in
      let vector_update destination destination_ctyp args =
        match args with
        | [source; index; element] -> (
            match (resolve source, scalar_integer index, resolve element) with
            | Some (Static_vector source), Some index, Some (Static_scalar element) -> (
                try
                  let index = Big_int.to_int index in
                  if index < 0 || index >= Array.length source then valid := false
                  else (
                    let updated = Array.copy source in
                    updated.(index) <- element;
                    match convert destination_ctyp (Static_vector updated) with
                    | Some value -> locals := NameMap.add destination value !locals
                    | None -> valid := false
                  )
                with _ -> valid := false
              )
            | _ -> valid := false
          )
        | _ -> valid := false
      in
      let fixed_bytes_of_integer length value =
        let byte_mask = Big_int.of_int 0xff in
        Static_vector
          (Array.init length (fun index ->
               let shift = 8 * (length - index - 1) in
               VL_int (Big_int.bitwise_and (Big_int.shift_right value shift) byte_mask)
           )
          )
      in
      let integer_conversion destination destination_ctyp args =
        match args with [source] -> assign destination destination_ctyp source | _ -> valid := false
      in
      let word_to_fixed_bytes destination destination_ctyp args =
        match (c_repr_fixed_bytes_length destination_ctyp, args) with
        | Some destination_length, [source] -> (
            match scalar_integer source with
            | Some value -> locals := NameMap.add destination (fixed_bytes_of_integer destination_length value) !locals
            | None -> valid := false
          )
        | _ -> valid := false
      in
      let static_evaluator function_id =
        match Bindings.find_opt function_id Config.c_static_evaluators with
        | Some operation -> Some operation
        | None ->
            (* Representation specialization can clone a declaration under a
               fresh identifier while retaining its emitted C name.  Static
               evaluator annotations belong to that operation, so resolve the
               clone by its source spelling as well as by identifier identity. *)
            let function_name = string_of_id function_id in
            Bindings.bindings Config.c_static_evaluators
            |> List.find_map (fun (annotated_id, operation) ->
                if String.equal (string_of_id annotated_id) function_name then Some operation else None
            )
      in
      let rec evaluate (I_aux (instr, _)) =
        if !valid then (
          match instr with
          | I_decl _ | I_clear _ | I_label _ | I_comment _ -> ()
          | I_block instrs -> List.iter evaluate instrs
          | I_init (_, destination, Init_cval value) | I_reinit (_, destination, value) ->
              let destination_ctyp =
                match instr with I_init (ctyp, _, _) | I_reinit (ctyp, _, _) -> ctyp | _ -> assert false
              in
              assign destination destination_ctyp value
          | I_copy (CL_id (destination, destination_ctyp), value) -> assign destination destination_ctyp value
          | I_funcall (CR_one (CL_id (destination, destination_ctyp)), _, (function_id, _), args) -> (
              match string_of_id function_id with
              | "vector_init" | "internal_vector_init" -> vector_init destination destination_ctyp args
              | "vector_update" | "vector_update_inc" | "internal_vector_update" ->
                  vector_update destination destination_ctyp args
              | "u256_of_fbits" | "u256_of_u128" -> integer_conversion destination destination_ctyp args
              | _ -> (
                  match static_evaluator function_id with
                  | Some "word_to_fixed_bytes" -> word_to_fixed_bytes destination destination_ctyp args
                  | Some _ | None -> valid := false
                )
            )
          | _ -> valid := false
        )
      in
      List.iter evaluate instrs;
      if not !valid then None
      else (
        let initializers =
          List.filter_map
            (fun (id, ctyp) ->
              Option.bind
                (NameMap.find_opt (name id) !globals)
                (fun value ->
                  match value with
                  | Static_vector elements when Array.exists (fun value -> value = VL_undefined) elements -> None
                  | value -> Some (id, ctyp, value)
                )
            )
            bindings
        in
        if List.length initializers = List.length bindings then Some initializers else None
      )
    )

  let prepare_static_letbinds ctx cdefs =
    static_letbinds := [];
    if Config.optimized_model then (
      let candidates =
        List.filter_map
          (function CDEF_aux (CDEF_let (number, bindings, instrs), _) -> Some (number, bindings, instrs) | _ -> None)
          cdefs
      in
      let rec discover known discovered pending =
        let progress, known, discovered, pending =
          List.fold_left
            (fun (progress, known, discovered, pending) ((number, bindings, instrs) as candidate) ->
              match static_letbind_initializers ~known_globals:known ctx bindings instrs with
              | None ->
                  if !Jib_compile.opt_debug_function_representations then
                    Printf.eprintf "C static let: retained runtime initializer=%d bindings=[%s]\n%!" number
                      (Util.string_of_list "," (fun (id, _) -> string_of_id id) bindings);
                  (progress, known, discovered, candidate :: pending)
              | Some initializers ->
                  let known =
                    List.fold_left (fun known (id, _, value) -> NameMap.add (name id) value known) known initializers
                  in
                  (true, known, (number, initializers) :: discovered, pending)
            )
            (false, known, discovered, []) pending
        in
        if progress then discover known discovered (List.rev pending) else List.rev discovered
      in
      static_letbinds := discover NameMap.empty [] candidates
    )

  (* A top-level let makes the stored C object immutable. For pointer-backed
     representations that means a const pointer, not a pointer to const data:
     Sail's value may still denote mutable host storage. *)
  let static_const_ctyp ctyp =
    if is_c_repr_byte_pointer ctyp then sgen_ctyp ctyp ^ " const" else "const " ^ sgen_ctyp ctyp

  let codegen_static_let_definition id ctyp = function
    | Static_scalar literal ->
        string (Printf.sprintf "%s %s = %s;" (static_const_ctyp ctyp) (sgen_id id) (sgen_value ctyp literal))
    | Static_vector elements ->
        if is_c_repr_fixed_bytes_u64_lanes ctyp then (
          let length = Option.get (c_repr_fixed_bytes_u64_lanes_length ctyp) in
          if length <> Array.length elements then c_error "fixed-byte lane initializer has the wrong length";
          let lanes = Array.make ((length + 7) / 8) Big_int.zero in
          Array.iteri
            (fun index literal ->
              let value =
                match literal with VL_int value -> Some value | VL_bits bits -> bit_literal_integer bits | _ -> None
              in
              match value with
              | Some value when Big_int.less_equal Big_int.zero value && Big_int.less_equal value (Big_int.of_int 0xff)
                ->
                  let shifted = Big_int.shift_left value (8 * (index mod 8)) in
                  lanes.(index / 8) <- Big_int.bitwise_or lanes.(index / 8) shifted
              | _ -> c_error "fixed-byte lane initializer contains a non-byte value"
            )
            elements;
          let lane_lines =
            Array.to_list lanes
            |> List.map (fun lane -> "UINT64_C(" ^ Big_int.to_string lane ^ ")")
            |> String.concat ",\n      "
          in
          string
            (Printf.sprintf "%s %s = {\n  .lanes = {\n      %s\n  },\n};" (static_const_ctyp ctyp) (sgen_id id)
               lane_lines
            )
        )
        else (
          let element_ctyp, length_field, data_field =
            match ctyp with
            | CT_fvector (length, element_ctyp) when length = Array.length elements ->
                (element_ctyp, Some length, "data")
            | ctyp when is_c_repr_fixed_bytes ctyp -> (
                match c_repr_fixed_bytes_length ctyp with
                | Some length when length = Array.length elements -> (CT_fbits 8, None, "bytes")
                | _ -> c_error "fixed-byte static initializer has the wrong length"
              )
            | _ -> c_error "static vector initializer has a non-fixed representation"
          in
          let rec chunks size values =
            match values with
            | [] -> []
            | values ->
                let chunk = Util.take size values in
                chunk :: chunks size (Util.drop size values)
          in
          let element_lines =
            Array.to_list elements
            |> List.map (sgen_value element_ctyp)
            |> chunks 8
            |> List.map (String.concat ", ")
            |> String.concat ",\n      "
          in
          let length_line =
            match length_field with Some length -> Printf.sprintf "  .len = %d,\n" length | None -> ""
          in
          string
            (Printf.sprintf "%s %s = {\n%s  .%s = {\n      %s\n  },\n};" (static_const_ctyp ctyp) (sgen_id id)
               length_line data_field element_lines
            )
        )

  let codegen_def' ctx (CDEF_aux (aux, _)) =
    match aux with
    | CDEF_register (id, _, _) when register_file_member id ->
        (* This register is a member of the model register file: its field,
           the struct's extern declaration, and its FFI compatibility macro
           are all emitted once by the anchor module (see
           [codegen_register_file_docs]); its storage is the single
           [struct model_registers model_registers] definition. *)
        []
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
        let is_fatal_error = String.equal function_name "fatal_error" in
        let parameter_names =
          match Bindings.find_opt id !function_parameter_names with
          | Some names when List.length names = List.length arg_ctyps -> names
          | _ when Option.is_some external_name ->
              List.mapi (fun index _ -> Printf.sprintf "/* arg_%d */" index) arg_ctyps
          | _ -> List.mapi (fun index _ -> Printf.sprintf "arg_%d" index) arg_ctyps
        in
        let parameters = List.map2 (fun ctyp name -> (ctyp, name)) arg_ctyps parameter_names in
        let thread_regs = Option.is_none external_name && register_file_threaded_function id in
        (* Hand-written FFI translation units keep calling threaded functions
           with their canonical argument lists: next to each declaration the
           header defines a guarded function-like macro that passes the
           register-file base implicitly.  The macro name being expanded is not
           rescanned (C11 6.10.3.4), and the GNU [, ##__VA_ARGS__] comma
           deletion covers zero-argument calls.  Generated translation units
           define the guard and spell the leading argument directly instead. *)
        let with_call_compat declaration =
          if not thread_regs then [FunctionDeclaration declaration]
          else
            [
              FunctionDeclaration
                (declaration ^^ hardline
                ^^ string (Printf.sprintf "#ifndef %s" (register_file_compat_guard ()))
                ^^ hardline
                ^^ string
                     (Printf.sprintf "#define %s(...) %s(&%s, ##__VA_ARGS__)" function_name function_name
                        register_file_variable
                     )
                ^^ hardline ^^ string "#endif"
                );
            ]
        in
        if is_fatal_error then
          [
            FunctionDeclaration
              (string (Printf.sprintf "_Noreturn void %s(%s);" function_name (c_parameter_list parameters)));
          ]
        else if Option.is_some external_name && not Config.optimized_model then []
        else if erase_unit_values && ctyp_equal ret_ctyp CT_unit then
          with_call_compat
            (string (Printf.sprintf "void %s(%s);" function_name (c_parameter_list ~thread_regs parameters)))
        else if is_stack_ctyp ctx ret_ctyp then
          with_call_compat
            (string
               (Printf.sprintf "%s %s(%s);" (sgen_ctyp ret_ctyp) function_name
                  (c_parameter_list ~thread_regs parameters)
               )
            )
        else (
          let ordinary_args = c_parameter_items parameters in
          let ordinary_args = (sgen_ctyp ret_ctyp ^ " *rop") :: ordinary_args in
          let ordinary_args = if thread_regs then register_file_thread_parameter :: ordinary_args else ordinary_args in
          let parameters = extra_params () ^ String.concat ", " ordinary_args in
          with_call_compat (string (Printf.sprintf "void %s(%s);" function_name parameters))
        )
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

          (* Falling off the end of a C [void] function is equivalent to an
             explicit [return;].  JIB still needs its unit-valued return while
             control flow is being analysed, but retaining that administrative
             instruction in the final optimized C creates noise in virtually
             every unit function.  A terminal call assigned directly to JIB's
             return destination is the same case: preserve the call and discard
             only the erased unit result.  Early returns remain untouched. *)
          let instrs =
            if
              Config.optimized_model && (not Config.cpp)
              && (match ret_arg with Return_plain -> true | Return_via _ -> false)
              && erase_unit_values && ctyp_equal ret_ctyp CT_unit
            then (
              match List.rev instrs with
              | I_aux (I_return value, _) :: reversed when ctyp_equal (cval_ctyp value) CT_unit -> List.rev reversed
              | I_aux (I_funcall (CR_one (CL_id (Return _, call_ctyp)), extern, callee, call_args), aux) :: reversed
                when ctyp_equal call_ctyp CT_unit ->
                  List.rev (I_aux (I_funcall (CR_one (CL_void call_ctyp), extern, callee, call_args), aux) :: reversed)
              | _ -> instrs
            )
            else instrs
          in

          (* Threaded functions spell member-register accesses through their
             [regs] parameter for the whole body being rendered here. *)
          let thread_regs = register_file_threaded_function id in
          current_function_threaded := thread_regs;
          let named_parameters = List.map2 (fun ctyp arg -> (ctyp, sgen_name arg)) arg_ctyps args in
          let referenced =
            List.fold_left
              (fun referenced instr -> NameSet.union referenced (instr_ids ~direct:false instr))
              NameSet.empty instrs
          in
          let unused_parameters =
            if Config.optimized_model && not Config.cpp then
              List.map2
                (fun (ctyp, parameter) jib_name ->
                  if (erase_unit_values && ctyp_equal ctyp CT_unit) || NameSet.mem jib_name referenced then None
                  else Some (string (Printf.sprintf "  (void)%s;" parameter))
                )
                named_parameters args
              |> List.filter_map Fun.id
            else []
          in
          let unused_parameter_markers = separate hardline unused_parameters in
          let c_args = c_parameter_list ~thread_regs named_parameters in
          let function_header =
            match ret_arg with
            | Return_plain ->
                assert (is_stack_ctyp ctx ret_ctyp);
                string (if erase_unit_values && ctyp_equal ret_ctyp CT_unit then "void" else sgen_ctyp ret_ctyp)
                ^^ space
                ^^ string (class_impl_prefix ())
                ^^ codegen_function_id id
                ^^ parens (string c_args)
                ^^ hardline
            | Return_via gs ->
                assert (not (is_stack_ctyp ctx ret_ctyp));
                let ordinary_args = c_parameter_items named_parameters in
                let ordinary_args = (sgen_ctyp ret_ctyp ^ " *" ^ sgen_name gs) :: ordinary_args in
                let ordinary_args =
                  if thread_regs then register_file_thread_parameter :: ordinary_args else ordinary_args
                in
                let return_via_args = extra_params () ^ String.concat ", " ordinary_args in
                string "void" ^^ space
                ^^ string (class_impl_prefix ())
                ^^ codegen_function_id id
                ^^ parens (string return_via_args)
                ^^ hardline
          in
          let definition =
            FunctionDefinition
              (function_header ^^ string "{" ^^ hardline ^^ unused_parameter_markers
              ^^ (if Util.list_empty unused_parameters then empty else hardline)
              ^^ codegen_instrs ~function_tail:true id ctx instrs
              ^^ hardline ^^ string "}"
              )
          in
          current_function_threaded := false;
          [definition]
        )
    | CDEF_type ctype_def ->
        let docs = codegen_type_def ctx ctype_def in
        if Config.optimized_model && Bindings.mem (ctype_def_id ctype_def) Config.external_type_names then []
        else if Config.optimized_model && Bindings.mem (ctype_def_id ctype_def) Config.external_types then
          List.filter (function TypeDeclaration _ -> false | _ -> true) docs
        else docs
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
          ^^ jump 0 2 (codegen_instrs id ctx instrs)
          ^^ hardline ^^ string "}"
        in
        let finish_decl = string (Printf.sprintf "void finish_%s(void);" (sgen_function_id id)) in
        if Config.cpp then [FunctionDefinition finish_impl; FunctionDeclaration finish_decl]
        else [FunctionDefinition finish_impl]
    | CDEF_let (number, bindings, instrs) -> (
        match static_letbind number with
        | Some initializers ->
            let variable_defs =
              separate_map hardline (fun (id, ctyp, value) -> codegen_static_let_definition id ctyp value) initializers
              ^^ hardline
            in
            let variable_decls =
              separate_map hardline
                (fun (id, ctyp, _) -> string (Printf.sprintf "extern %s %s;" (static_const_ctyp ctyp) (sgen_id id)))
                initializers
              ^^ hardline
            in
            [VariableDeclaration variable_decls; VariableDefinition variable_defs]
        | None ->
            let setup = List.concat (List.map (fun (id, ctyp) -> [idecl (id_loc id) ctyp (name id)]) bindings) in
            let cleanup =
              List.concat (List.map (fun (id, ctyp) -> [iclear ~loc:(id_loc id) ctyp (name id)]) bindings)
            in
            let variable_defs =
              separate_map hardline
                (fun (id, ctyp) ->
                  string (Printf.sprintf "%s %s%s;" (sgen_ctyp ctyp) (sgen_id id) (variable_zero_init ()))
                )
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
              ^^ jump 0 2 (codegen_instrs (mk_id "let") { ctx with no_raw = true } instrs)
              ^^ hardline ^^ string "}" ^^ hardline
              ^^ string (Printf.sprintf "void %skill_letbind_%d(void) " (class_impl_prefix ()) number)
              ^^ string "{"
              ^^ jump 0 2 (codegen_instrs (mk_id "let") ctx cleanup)
              ^^ hardline ^^ string "}"
            in

            (if Config.optimized_model then [VariableDeclaration variable_decls] else [])
            @ [VariableDefinition variable_defs; FunctionDeclaration function_decls; FunctionDefinition impl]
      )
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
    | CTG_fixed_bytes_u64_lanes of int
    | CTG_tup of ctyp list
    | CTG_list of ctyp
    | CTG_vector of ctyp
    | CTG_fixed_vector of int * ctyp

  let rec ctyp_dependencies = function
    | ctyp when is_c_repr_byte_pointer ctyp -> []
    | CT_fint _ | CT_fuint _ -> [CTG_native_int_conversion_failure]
    | ctyp when is_c_repr_u128 ctyp -> [CTG_native_int_conversion_failure; CTG_u128]
    | ctyp when is_c_repr_u256 ctyp -> [CTG_native_int_conversion_failure; CTG_u256]
    | ctyp when is_c_repr_u320 ctyp -> [CTG_native_int_conversion_failure; CTG_u320]
    | ctyp when is_c_repr_fixed_bytes_u64_lanes ctyp ->
        [CTG_fixed_bytes_u64_lanes (Option.get (c_repr_fixed_bytes_u64_lanes_length ctyp))]
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
    | CTG_fixed_bytes_u64_lanes length -> codegen_fixed_bytes_u64_lanes length
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
    let type_decls, func_decls, func_defs, var_decls, var_defs, static_func_defs =
      List.fold_left
        (fun (type_decls, func_decls, func_defs, var_decls, var_defs, static_func_defs) -> function
          | TypeDeclaration doc -> (doc :: type_decls, func_decls, func_defs, var_decls, var_defs, static_func_defs)
          | FunctionDeclaration doc -> (type_decls, doc :: func_decls, func_defs, var_decls, var_defs, static_func_defs)
          | FunctionDefinition doc -> (type_decls, func_decls, doc :: func_defs, var_decls, var_defs, static_func_defs)
          | VariableDeclaration doc -> (type_decls, func_decls, func_defs, doc :: var_decls, var_defs, static_func_defs)
          | VariableDefinition doc -> (type_decls, func_decls, func_defs, var_decls, doc :: var_defs, static_func_defs)
          | StaticFunctionDefinition doc | DemandedStaticFunctionDefinition (_, doc) ->
              (type_decls, func_decls, func_defs, var_decls, var_defs, doc :: static_func_defs)
          )
        ([], [], [], [], [], []) docs
    in
    let merge_reverse docs =
      match docs with [] -> empty | docs -> separate (twice hardline) (List.rev docs) ^^ twice hardline
    in
    {
      type_decl = merge_reverse type_decls;
      func_decl = merge_reverse func_decls;
      func_def = merge_reverse func_defs;
      var_decl = merge_reverse var_decls;
      var_def = merge_reverse var_defs;
      static_func_def = merge_reverse static_func_defs;
    }

  (** When we generate code for a definition, we need to first generate any auxillary type definitions that are
      required. *)
  let codegen_def ctx def =
    match def with
    | CDEF_aux (CDEF_type ctype_def, _)
      when Config.optimized_model && Bindings.mem (ctype_def_id ctype_def) Config.external_type_names ->
        []
    | CDEF_aux ((CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _)), _)
      when ctx_is_extern id ctx && not Config.optimized_model ->
        []
    | _ ->
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
          let dependency_docs = List.concat (List.map (codegen_ctg ctx) deps) in
          let definition_docs = codegen_def' ctx def in
          dependency_docs @ definition_docs
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
    optimize_stack_aggregates := Config.optimized_model;
    c_repr_external_value_types :=
      Bindings.fold (fun id _ types -> IdSet.add id types) Config.external_type_names IdSet.empty;
    let module Jibc = Make (C_config (struct
      let branch_coverage = Config.branch_coverage
      let assert_to_exception = Config.assert_to_exception
      let preserve_types = Config.preserve_types
      let c_repr_unsigned = Config.c_repr_unsigned
      let c_repr_signed = Config.c_repr_signed
      let c_repr_u256 = Config.c_repr_u256
      let c_repr_fixed_bytes = Config.c_repr_fixed_bytes
      let c_repr_fixed_bytes_u64_lanes = Config.c_repr_fixed_bytes_u64_lanes
      let c_repr_fixed_bytes_u64_lane_alias_lengths = Config.c_repr_fixed_bytes_u64_lane_alias_lengths
      let byte_pointer_fields = Config.byte_pointer_fields
      let byte_pointer_types = Config.byte_pointer_types
      let byte_pointer_signatures = Config.byte_pointer_signatures
      let fixed_bytes_signatures = Config.fixed_bytes_signatures
      let fixed_bytes_u64_lanes_signatures = Config.fixed_bytes_u64_lanes_signatures
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

  (* Select the model register file members before any definition is rendered:
     [sgen_name] consults the member set for every register reference.
     Membership follows source declaration order (the definitions were just
     stable-sorted by module), except that measured-hot registers from
     [register_file_hot_priority] are hoisted to the front of the struct.
     Registers owned by an excluded module keep the plain-global emission.
     The anchor is the last module that declares a member register: its header
     transitively includes every earlier module header, so all member types
     are complete there, and any translation unit that could previously see a
     member register's extern declaration also sees the anchor's struct
     definition and compatibility macros. *)
  let prepare_register_file (modules : c_module array) module_index cdefs =
    let members, anchor =
      List.fold_left
        (fun (members, anchor) annotated ->
          match annotated with
          | CDEF_aux (CDEF_register (reg, ctyp, _), _) ->
              let index = module_index annotated in
              if List.mem modules.(index).file_stem Config.register_file_excluded_modules then (members, anchor)
              else ((reg, ctyp) :: members, max anchor index)
          | _ -> (members, anchor)
        )
        ([], -1) cdefs
    in
    let members = List.rev members in
    let priority (reg, _) =
      let symbol = sgen_register_file_symbol reg in
      let rec find rank = function
        | [] -> Stdlib.max_int
        | hot :: hots -> if String.equal hot symbol then rank else find (rank + 1) hots
      in
      find 0 register_file_hot_priority
    in
    let members = List.stable_sort (fun left right -> Int.compare (priority left) (priority right)) members in
    register_file_members := members;
    register_file_member_ids :=
      List.fold_left
        (fun ids (reg, _) -> match reg with Name (id, _) -> IdSet.add id ids | _ -> ids)
        IdSet.empty members;
    register_file_anchor_index := anchor

  (* Select the threaded functions (--c-register-file-thread) after the member
     set is fixed: a generated function is threaded exactly when its own body
     reads or writes a member register.  Entry points reached from hand-written
     FFI or from the generated model_init keep their existing signatures and
     stay unthreaded: zmain, every --c-preserve function, and the register and
     configuration initializers called by [gen_model_init_fini]'s hand-emitted
     statements. *)
  let prepare_register_file_threading cdefs =
    let entry_points =
      IdSet.union Config.preserved_functions
        (IdSet.of_list [mk_id "main"; mk_id "initialize_registers"; mk_id "__InitConfig"])
    in
    let accesses_member_register body =
      let names =
        List.fold_left (fun names instr -> NameSet.union names (instr_ids ~direct:false instr)) NameSet.empty body
      in
      NameSet.exists (function Name (id, _) -> IdSet.mem id !register_file_member_ids | _ -> false) names
    in
    register_file_threaded_functions :=
      List.fold_left
        (fun threaded (CDEF_aux (aux, _)) ->
          match aux with
          | CDEF_fundef (id, _, _, body) when (not (IdSet.mem id entry_points)) && accesses_member_register body ->
              IdSet.add id threaded
          | _ -> threaded
        )
        IdSet.empty cdefs

  (* The anchor module's register-file block: the struct declaration and its
     extern (header), the guarded FFI compatibility macros (header), and the
     single storage definition (implementation).  File-scope storage is
     zero-initialized like the plain globals it replaces; the Sail-level
     initial values still run in initialize_registers()/model_init(). *)
  let codegen_register_file_docs () =
    if !register_file_members = [] then []
    else (
      let fields =
        List.map
          (fun (reg, ctyp) -> Printf.sprintf "  %s %s;" (sgen_ctyp ctyp) (sgen_register_file_symbol reg))
          !register_file_members
      in
      let macros =
        List.map
          (fun (reg, _) ->
            let symbol = sgen_register_file_symbol reg in
            Printf.sprintf "#define %s (%s.%s)" symbol register_file_variable symbol
          )
          !register_file_members
      in
      let declaration =
        List.map string
          ([
             "// Model register file (--c-register-file): every model register outside the";
             "// configured excluded modules is a member of this struct, so all register";
             "// accesses share one base address instead of one address materialization per";
             "// distinct global.  Hot registers are placed first; the remaining members";
             "// follow their Sail source declaration order.";
             Printf.sprintf "struct %s {" register_file_variable;
           ]
          @ fields
          @ [
              "};";
              Printf.sprintf "extern struct %s %s;" register_file_variable register_file_variable;
              "";
              Printf.sprintf "#ifndef %s" (register_file_compat_guard ());
              "// Compatibility aliases so hand-written FFI keeps naming registers directly.";
              "// The member token after '.' is the macro currently being expanded and is";
              "// not rescanned, so the self-reference is well-defined.  Generated";
              "// translation units define the guard and spell members directly instead.";
            ]
          @ macros @ ["#endif"]
          )
        |> separate hardline
      in
      [
        VariableDeclaration declaration;
        VariableDefinition (string (Printf.sprintf "struct %s %s;" register_file_variable register_file_variable));
      ]
    )

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

    let static_letbinds =
      List.filter_map
        (function
          | CDEF_aux (CDEF_let (number, _, _), _) when Option.is_some (static_letbind number) -> Some number | _ -> None
          )
        cdefs
    in
    let runtime_letbinds = List.filter (fun number -> not (List.mem number static_letbinds)) ctx.letbinds in
    let letbind_initializers =
      List.map (fun n -> Printf.sprintf "  create_letbind_%d();" n) (List.rev runtime_letbinds)
    in
    let letbind_finalizers = List.map (fun n -> Printf.sprintf "  kill_letbind_%d();" n) runtime_letbinds in

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
           @ (if Config.optimized_model then [] else ["  setup_rts();"] @ fst exn_boilerplate)
           @ List.concat (List.map (fun r -> fst (register_init_clear r)) early_regs)
           @ set_abstract_types @ startup cdefs @ letbind_initializers
           @ List.concat (List.map (fun r -> fst (register_init_clear r)) regs)
           @ ( if regs = [] then []
               else
                 [
                   Printf.sprintf "  %s(%s);"
                     (sgen_function_id (mk_id "initialize_registers"))
                     (if erase_unit_values then "" else "UNIT");
                 ]
             )
           @ ( if ctx_has_val_spec init_config_id ctx then
                 [
                   Printf.sprintf "  %s(%s);" (sgen_function_id init_config_id)
                     (if erase_unit_values then "" else "UNIT");
                 ]
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

  (* Representation inference may discover several proof-bound partitions for
     one typed Sail function even when optimization leaves them with precisely
     the same represented signature and JIB body.  Those partitions remain
     distinct in the specialization plan, but they do not need distinct C
     definitions.  Coalesce only after the final JIB optimization, and use a
     partition refinement over specialized callees so recursive and mutually
     dependent definitions are compared without their proof-bound names. *)
  let deduplicate_representation_specializations ctx cdefs =
    let traces_by_id =
      List.fold_left
        (fun traces (trace : Jib_compile.representation_specialization) ->
          Bindings.add trace.specialized_id trace traces
        )
        Bindings.empty
        !Jib_compile.representation_specializations
    in
    let definitions =
      List.filter_map
        (function
          | CDEF_aux (CDEF_fundef (id, heap_return, parameters, instrs), _) when Bindings.mem id traces_by_id ->
              Some (id, Bindings.find id traces_by_id, heap_return, parameters, instrs)
          | _ -> None
          )
        cdefs
    in
    let emitted_signatures_by_id =
      List.fold_left
        (fun signatures -> function
          | CDEF_aux (CDEF_val (id, _, parameter_types, result_type, _), _) when Bindings.mem id traces_by_id ->
              Bindings.add id (parameter_types, result_type) signatures
          | _ -> signatures
          )
        Bindings.empty cdefs
    in
    let emitted_signature (id, _, _, _, _) = Bindings.find id emitted_signatures_by_id in
    let signature_key ((_, trace, _, _, _) as definition) =
      let parameter_types, result_type = emitted_signature definition in
      String.concat "\x1f"
        [
          string_of_id trace.Jib_compile.source_id;
          String.concat "," (List.map sgen_ctyp parameter_types);
          sgen_ctyp result_type;
        ]
    in
    let minimum_id left right = if Id.compare left right <= 0 then left else right in
    let representatives_for key definitions =
      let minima =
        List.fold_left
          (fun minima ((id, _, _, _, _) as definition) ->
            let key = key definition in
            Util.StringMap.update key (function None -> Some id | Some prior -> Some (minimum_id prior id)) minima
          )
          Util.StringMap.empty definitions
      in
      List.fold_left
        (fun representatives ((id, _, _, _, _) as definition) ->
          Bindings.add id (Util.StringMap.find (key definition) minima) representatives
        )
        Bindings.empty definitions
    in
    let initial_representatives = representatives_for signature_key definitions in
    let normalize_call representatives = function
      | I_aux (I_funcall (result, Call _, (callee, type_arguments), arguments), annot) ->
          let callee = Option.value ~default:callee (Bindings.find_opt callee representatives) in
          I_aux (I_funcall (result, Call (([], None), []), (callee, type_arguments), arguments), annot)
      | I_aux (I_funcall (result, kind, (callee, type_arguments), arguments), annot) ->
          let callee = Option.value ~default:callee (Bindings.find_opt callee representatives) in
          I_aux (I_funcall (result, kind, (callee, type_arguments), arguments), annot)
      | instr -> instr
    in
    let body_key representatives ((id, _, heap_return, parameters, instrs) as definition) =
      let prior = Option.value ~default:id (Bindings.find_opt id representatives) in
      let heap_return_key =
        match heap_return with
        | Return_plain -> "return:plain"
        | Return_via name -> "return:heap:" ^ string_of_name ~zencode:false name
      in
      let parameters_key = String.concat "," (List.map (string_of_name ~zencode:false) parameters) in
      let body =
        map_instr_list (normalize_call representatives) instrs |> List.map string_of_instr |> String.concat "\n"
      in
      String.concat "\x1e" [signature_key definition; string_of_id prior; heap_return_key; parameters_key; body]
    in
    let rec refine representatives =
      let refined = representatives_for (body_key representatives) definitions in
      if Bindings.equal (fun left right -> Id.compare left right = 0) representatives refined then refined
      else refine refined
    in
    let representatives = refine initial_representatives in
    let classes_by_signature =
      List.fold_left
        (fun classes ((id, _, _, _, _) as definition) ->
          let representative = Bindings.find id representatives in
          Util.StringMap.update (signature_key definition)
            (function
              | None -> Some (IdSet.singleton representative)
              | Some representatives -> Some (IdSet.add representative representatives)
              )
            classes
        )
        Util.StringMap.empty definitions
    in
    let specialized_ids = List.fold_left (fun ids (id, _, _, _, _) -> IdSet.add id ids) IdSet.empty definitions in
    let occupied_ids =
      List.fold_left
        (fun ids -> function
          | CDEF_aux
              ((CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _) | CDEF_startup (id, _) | CDEF_finish (id, _)), _)
            when not (IdSet.mem id specialized_ids) ->
              IdSet.add id ids
          | _ -> ids
          )
        IdSet.empty cdefs
    in
    let definition_for_id id = List.find (fun (candidate, _, _, _, _) -> Id.compare candidate id = 0) definitions in
    let classes_by_source =
      Util.StringMap.fold
        (fun _ representatives classes ->
          IdSet.fold
            (fun representative classes ->
              let _, trace, _, _, _ = definition_for_id representative in
              let source = string_of_id trace.Jib_compile.source_id in
              Util.StringMap.update source
                (function None -> Some [representative] | Some prior -> Some (representative :: prior))
                classes
            )
            representatives classes
        )
        classes_by_signature Util.StringMap.empty
    in
    let signature_stem definition =
      (* These components are embedded inside a larger function identifier, so
         C type names such as uint8_t and bool are safe here even though the
         ordinary standalone-name sanitizer quite correctly reserves them. *)
      let stem ctyp =
        let buffer = Buffer.create 32 in
        let separator () =
          let length = Buffer.length buffer in
          if length > 0 && Buffer.nth buffer (length - 1) <> '_' then Buffer.add_char buffer '_'
        in
        String.iter
          (fun character ->
            match character with
            | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_') as character -> Buffer.add_char buffer character
            | '*' ->
                separator ();
                Buffer.add_string buffer "ptr"
            | _ -> separator ()
          )
          (sgen_ctyp ctyp);
        let stem = Buffer.contents buffer in
        if stem = "" then "value" else stem
      in
      let parameter_types, result_type = emitted_signature definition in
      let parameters =
        match parameter_types with [] -> "void" | parameters -> String.concat "_" (List.map stem parameters)
      in
      parameters ^ "_to_" ^ stem result_type
    in
    let representative_outputs =
      Util.StringMap.fold
        (fun source representatives outputs ->
          let representatives = List.sort Id.compare representatives in
          let source_id =
            let _, trace, _, _, _ = definition_for_id (List.hd representatives) in
            trace.Jib_compile.source_id
          in
          if List.length representatives = 1 && not (IdSet.mem source_id occupied_ids) then
            Bindings.add (List.hd representatives) source_id outputs
          else (
            let by_signature =
              List.fold_left
                (fun signatures representative ->
                  let definition = definition_for_id representative in
                  Util.StringMap.update (signature_stem definition)
                    (function None -> Some [representative] | Some prior -> Some (representative :: prior))
                    signatures
                )
                Util.StringMap.empty representatives
            in
            Util.StringMap.fold
              (fun stem variants outputs ->
                List.sort Id.compare variants
                |> List.mapi (fun index representative ->
                    let suffix = if index = 0 then "" else Printf.sprintf "_variant_%d" (index + 1) in
                    (representative, mk_id (source ^ "_" ^ stem ^ suffix))
                )
                |> List.fold_left
                     (fun outputs (representative, output) -> Bindings.add representative output outputs)
                     outputs
              )
              by_signature outputs
          )
        )
        classes_by_source Bindings.empty
    in
    let output_ids =
      Bindings.fold
        (fun id representative outputs -> Bindings.add id (Bindings.find representative representative_outputs) outputs)
        representatives Bindings.empty
    in
    let rewrite_call = function
      | I_aux (I_funcall (result, kind, (callee, type_arguments), arguments), annot) ->
          let callee = Option.value ~default:callee (Bindings.find_opt callee output_ids) in
          I_aux (I_funcall (result, kind, (callee, type_arguments), arguments), annot)
      | instr -> instr
    in
    let emitted_valspecs = ref IdSet.empty and emitted_fundefs = ref IdSet.empty in
    let cdefs =
      List.filter_map
        (fun (CDEF_aux (cdef, def_annot) as annotated) ->
          let annotated = cdef_map_instr rewrite_call annotated in
          match cdef with
          | CDEF_val (id, type_parameters, parameter_types, result_type, extern) when Bindings.mem id output_ids ->
              let output = Bindings.find id output_ids in
              if IdSet.mem output !emitted_valspecs then None
              else (
                emitted_valspecs := IdSet.add output !emitted_valspecs;
                Some (CDEF_aux (CDEF_val (output, type_parameters, parameter_types, result_type, extern), def_annot))
              )
          | CDEF_fundef (id, heap_return, parameters, instrs) when Bindings.mem id output_ids ->
              let output = Bindings.find id output_ids in
              if IdSet.mem output !emitted_fundefs then None
              else (
                emitted_fundefs := IdSet.add output !emitted_fundefs;
                let instrs = map_instr_list rewrite_call instrs in
                Some (CDEF_aux (CDEF_fundef (output, heap_return, parameters, instrs), def_annot))
              )
          | _ -> Some annotated
        )
        cdefs
    in
    let valspecs =
      Bindings.fold
        (fun id output valspecs ->
          match Bindings.find_opt id ctx.valspecs with
          | Some valspec -> Bindings.add output valspec valspecs
          | None -> valspecs
        )
        output_ids ctx.valspecs
    in
    let removed = List.length definitions - IdSet.cardinal !emitted_fundefs in
    (cdefs, { ctx with valspecs }, output_ids, removed)

  (* Specialization and constant folding can erase the runtime use of a
     dependent proof/correlation parameter while leaving that parameter in
     the represented C signature.  For internal functions, remove such
     formals and the corresponding pure JIB call operands together.  Calls in
     JIB are already in three-address form, so dropping a cval operand cannot
     drop an effectful function call; any effectful producer remains as its
     own instruction.

     Preserved functions are part of the requested generated ABI and externs
     are host contracts, so neither may change arity.  Raw C is opaque to JIB
     dependency analysis and is therefore excluded as well.  Iterate because
     deleting an argument at one call can make a forwarding parameter in its
     caller dead on the next round. *)
  let remove_unused_internal_parameters ctx cdefs specialization_output_ids =
    let preserved_sources = IdSet.of_list (Specialize.get_initial_calls ()) in
    let preserved =
      List.fold_left
        (fun preserved (trace : Jib_compile.representation_specialization) ->
          if IdSet.mem trace.source_id preserved_sources then (
            let output =
              Option.value ~default:trace.specialized_id
                (Bindings.find_opt trace.specialized_id specialization_output_ids)
            in
            IdSet.add output preserved
          )
          else preserved
        )
        preserved_sources
        !Jib_compile.representation_specializations
    in
    let rec contains_raw instr =
      match instr with
      | I_aux (I_raw _, _) -> true
      | I_aux (I_if (_, then_instrs, else_instrs), _) ->
          List.exists contains_raw then_instrs || List.exists contains_raw else_instrs
      | I_aux ((I_block instrs | I_try_block instrs), _) -> List.exists contains_raw instrs
      | _ -> false
    in
    let referenced_names instrs =
      List.fold_left
        (fun referenced instr -> NameSet.union referenced (instr_ids ~direct:false instr))
        NameSet.empty instrs
    in
    let filter_mask mask values =
      if List.length mask <> List.length values then invalid_arg "remove_unused_internal_parameters"
      else List.fold_right2 (fun keep value kept -> if keep then value :: kept else kept) mask values []
    in
    let one_pass ctx cdefs =
      let candidate_masks =
        List.fold_left
          (fun masks -> function
            | CDEF_aux (CDEF_fundef (id, _, parameters, instrs), _)
              when Config.optimized_model
                   && (not (IdSet.mem id preserved))
                   && (not (ctx_is_extern id ctx))
                   && not (List.exists contains_raw instrs) ->
                let referenced = referenced_names instrs in
                let mask = List.map (fun parameter -> NameSet.mem parameter referenced) parameters in
                if List.for_all Fun.id mask then masks else Bindings.add id mask masks
            | _ -> masks
            )
          Bindings.empty cdefs
      in
      (* A late JIB call can intentionally expose a different operand list
         from the source-level valspec (for example after another ABI
         lowering).  Parameter pruning is only valid when every view of the
         function agrees on arity, so conservatively leave such functions
         unchanged. *)
      let invalid_masks = ref IdSet.empty in
      let validate_arity id values =
        match Bindings.find_opt id candidate_masks with
        | Some mask when List.length mask <> List.length values -> invalid_masks := IdSet.add id !invalid_masks
        | _ -> ()
      in
      let inspect_call = function
        | I_aux (I_funcall (_, _, (callee, _), arguments), _) as instr ->
            validate_arity callee arguments;
            instr
        | instr -> instr
      in
      List.iter
        (fun (CDEF_aux (cdef, _) as annotated) ->
          ( match cdef with
          | CDEF_val (id, _, parameter_types, _, _) -> validate_arity id parameter_types
          | CDEF_fundef (id, _, parameters, _) -> validate_arity id parameters
          | _ -> ()
          );
          ignore (cdef_map_instr inspect_call annotated)
        )
        cdefs;
      Bindings.iter (fun id (_, parameter_types, _, _) -> validate_arity id parameter_types) ctx.valspecs;
      let masks = IdSet.fold (fun id masks -> Bindings.remove id masks) !invalid_masks candidate_masks in
      if Bindings.is_empty masks then (cdefs, ctx, 0)
      else (
        let rewrite_call = function
          | I_aux (I_funcall (result, kind, (callee, type_arguments), arguments), annot) when Bindings.mem callee masks
            ->
              let arguments = filter_mask (Bindings.find callee masks) arguments in
              I_aux (I_funcall (result, kind, (callee, type_arguments), arguments), annot)
          | instr -> instr
        in
        let cdefs =
          List.map
            (fun (CDEF_aux (cdef, def_annot) as annotated) ->
              match cdef with
              | CDEF_val (id, type_parameters, parameter_types, result_type, extern) when Bindings.mem id masks ->
                  let parameter_types = filter_mask (Bindings.find id masks) parameter_types in
                  CDEF_aux (CDEF_val (id, type_parameters, parameter_types, result_type, extern), def_annot)
              | CDEF_fundef (id, heap_return, parameters, instrs) when Bindings.mem id masks ->
                  let mask = Bindings.find id masks in
                  let parameters = filter_mask mask parameters in
                  let instrs = map_instr_list rewrite_call instrs in
                  CDEF_aux (CDEF_fundef (id, heap_return, parameters, instrs), def_annot)
              | _ -> cdef_map_instr rewrite_call annotated
            )
            cdefs
        in
        let valspecs =
          Bindings.fold
            (fun id (extern, parameter_types, result_type, annot) valspecs ->
              let parameter_types =
                match Bindings.find_opt id masks with
                | Some mask -> filter_mask mask parameter_types
                | None -> parameter_types
              in
              Bindings.add id (extern, parameter_types, result_type, annot) valspecs
            )
            ctx.valspecs Bindings.empty
        in
        let removed =
          Bindings.fold
            (fun _ mask removed -> removed + List.fold_left (fun count keep -> if keep then count else count + 1) 0 mask)
            masks 0
        in
        (cdefs, { ctx with valspecs }, removed)
      )
    in
    let rec fixpoint cdefs ctx removed =
      let cdefs, ctx, removed_now = one_pass ctx cdefs in
      if removed_now = 0 then (cdefs, ctx, removed) else fixpoint cdefs ctx (removed + removed_now)
    in
    fixpoint cdefs ctx 0

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
      let ast = if !optimize_inline_attr then propagate_inline_attributes ast else ast in
      log_phase "lowering Sail AST to JIB";
      let cdefs, ctx = jib_of_ast env effect_info ast in
      log_phase "lowered JIB definitions=%d" (List.length cdefs);
      (* --c-inline-attr must run before insert_heap_returns rewrites the
         canonical JIB return protocol the generic inliner substitutes. *)
      let cdefs = if !optimize_inline_attr then inline_marked_functions cdefs else cdefs in
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
        optimize ~have_rts:(not Config.no_rts) ~specialize_c:Config.specialize_c ~optimized_model:Config.optimized_model
          ctx recursive_functions cdefs
      in
      let cdefs, ctx =
        if !optimize_dead_letbinds then (
          let cdefs, live_letbinds = remove_dead_letbinds cdefs in
          let dropped = List.length ctx.letbinds - List.length live_letbinds in
          if dropped > 0 then log_phase "removed dead letbinds=%d" dropped;
          (cdefs, { ctx with letbinds = List.filter (fun n -> List.mem n live_letbinds) ctx.letbinds })
        )
        else (cdefs, ctx)
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
      if Config.optimized_model && not (Bindings.is_empty Config.external_types) then (
        let type_definitions =
          List.fold_left
            (fun definitions -> function
              | CDEF_aux (CDEF_type ctype_def, _) -> Bindings.add (ctype_def_id ctype_def) ctype_def definitions
              | _ -> definitions
              )
            Bindings.empty cdefs
        in
        Bindings.iter
          (fun id _ ->
            match Bindings.find_opt id type_definitions with
            | None ->
                c_error
                  (Printf.sprintf
                     "external optimized-model type %s does not name a concrete type retained after specialization"
                     (string_of_id id)
                  )
            | Some (CTD_abstract _) ->
                c_error (Printf.sprintf "abstract Sail type %s cannot reuse an external C declaration" (string_of_id id))
            | Some (CTD_struct (_, params, _) | CTD_variant (_, params, _)) when not (Util.list_empty params) ->
                c_error
                  (Printf.sprintf
                     "polymorphic Sail type %s cannot reuse one external C declaration; map each concrete \
                      specialization"
                     (string_of_id id)
                  )
            | Some _ -> ()
          )
          Config.external_types;
        List.iter
          (fun (record_id, field_id, adapter) ->
            match Bindings.find_opt record_id type_definitions with
            | Some (CTD_struct (_, _, fields)) -> (
                match List.find_opt (fun (candidate, _) -> Id.compare field_id candidate = 0) fields with
                | Some (_, field_ctyp) when ctyp_equal field_ctyp (c_repr_const_byte_pointer_ctyp adapter) -> ()
                | Some _ ->
                    c_error
                      (Printf.sprintf "optimized byte-pointer field %s.%s is not represented as a byte pointer"
                         (string_of_id record_id) (string_of_id field_id)
                      )
                | None ->
                    c_error
                      (Printf.sprintf "optimized byte-pointer field %s.%s does not exist (available fields: %s)"
                         (string_of_id record_id) (string_of_id field_id)
                         (String.concat ", " (List.map (fun (id, _) -> string_of_id id) fields))
                      )
              )
            | Some _ ->
                c_error (Printf.sprintf "optimized byte-pointer owner %s is not a record" (string_of_id record_id))
            | None -> ()
          )
          Config.byte_pointer_fields
      );
      (* A named external optimized-model type deliberately delegates its
         complete representation to the supplied C declaration. Its canonical
         Sail fields may therefore contain managed values (for example a
         list-backed semantic collection) that never occur in the optimized
         ABI. Do not inspect that hidden definition or emit dependencies for
         it after validating the external mapping above. *)
      let managed_model_cdefs =
        List.filter
          (function
            | CDEF_aux (CDEF_type ctyp_def, _) -> not (Bindings.mem (ctype_def_id ctyp_def) Config.external_type_names)
            | _ -> true
            )
          cdefs
      in
      let has_sail_int = cdefs_contain ctx (function CT_lint -> true | _ -> false) managed_model_cdefs in
      let has_lbits = cdefs_contain ctx (function CT_lbits -> true | _ -> false) managed_model_cdefs in
      let has_sail_config =
        cdefs_contain ctx (function CT_json | CT_json_key -> true | _ -> false) managed_model_cdefs
      in
      let is_managed_ctyp = function
        | CT_lint | CT_lbits | CT_real | CT_string | CT_list _ | CT_vector _ | CT_memory_writes | CT_json | CT_json_key
          ->
            true
        | _ -> false
      in
      let has_managed_representation = cdefs_contain ctx is_managed_ctyp managed_model_cdefs in
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
            managed_model_cdefs
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
                | CDEF_type (CTD_struct (_, params, _) | CTD_variant (_, params, _)) -> not (Util.list_empty params)
                | CDEF_type (CTD_abbrev _) -> true
                | CDEF_val (id, _, _, _, _) | CDEF_fundef (id, _, _, _) -> ctx_is_extern id ctx
                | _ -> false
              in
              if (not ignored) && cdef_has_ctyp (ctyp_contains is_managed_ctyp) annotated then (
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
                Some (owner, def_annot.loc, managed_ctyp_names annotated)
              )
              else None
            )
            managed_model_cdefs
          |> Option.value ~default:("the generated model", Parse_ast.Unknown, [])
        in
        raise
          (Reporting.err_general loc
             (Printf.sprintf
                "C backend: --c-optimized-model requires every generated value to have a fixed, unmanaged C \n\
                 representation, but %s still contains an unbounded integer, dynamic bitvector/container, string, \n\
                 real, JSON value, memory-write log, or reference after specialization.%s"
                owner
                ( match managed_types with
                | [] -> ""
                | types -> " Managed JIB representation(s): " ^ String.concat ", " types ^ "."
                )
             )
          )
      );
      emit_generic_sail_int_helpers := (not Config.specialize_c) || has_sail_int;
      emit_generic_lbits_helpers := (not Config.specialize_c) || has_lbits;
      let language_exceptions = ref false in
      let exception_visitor =
        object
          inherit empty_jib_visitor

          method! vinstr =
            function
            | I_aux ((I_throw _ | I_try_block _), _) ->
                language_exceptions := true;
                SkipChildren
            | _ -> DoChildren
        end
      in
      ignore (visit_cdefs exception_visitor cdefs);
      emit_optimized_exception_state := (not Config.optimized_model) || !language_exceptions;

      let specialization_plan =
        if
          Option.is_some Config.specialization_plan_json
          || Option.is_some Config.specialization_plan_human
          || Option.is_some Config.specialization_obligations_lean
          || Option.is_some Config.specialization_obligations_coq
        then (
          let ids ids = IdSet.elements ids |> List.map string_of_id |> String.concat "," in
          let ids_at_width width bindings =
            Bindings.bindings bindings
            |> List.filter_map (fun (id, configured_width) -> if configured_width = width then Some id else None)
            |> IdSet.of_list |> ids
          in
          let non_64_native_reprs key bindings =
            let reprs =
              Bindings.bindings bindings
              |> List.filter_map (fun (id, width) ->
                  if width = 64 then None else Some (string_of_id id ^ ":" ^ string_of_int width)
              )
            in
            match reprs with [] -> [] | _ -> [key ^ "=" ^ String.concat "," reprs]
          in
          let fixed_bytes =
            Bindings.bindings Config.c_repr_fixed_bytes
            |> List.map (fun (id, length) -> string_of_id id ^ ":" ^ string_of_int length)
            |> String.concat ","
          in
          let configuration =
            String.concat ";"
              ([
                 "specialize_c=" ^ string_of_bool Config.specialize_c;
                 "require_bounded_int=" ^ string_of_bool Config.require_bounded_int;
                 "preserved_calls=" ^ ids (IdSet.of_list (Specialize.get_initial_calls ()));
                 "c_repr_uint64=" ^ ids_at_width 64 Config.c_repr_unsigned;
                 "c_repr_int64=" ^ ids_at_width 64 Config.c_repr_signed;
                 "c_repr_u256=" ^ ids Config.c_repr_u256;
                 "c_repr_fixed_bytes=" ^ fixed_bytes;
               ]
              @ non_64_native_reprs "c_repr_unsigned_non64" Config.c_repr_unsigned
              @ non_64_native_reprs "c_repr_signed_non64" Config.c_repr_signed
              )
          in
          Some
            (Specialization_plan.create ~compiler_name:"Sail" ~compiler_version:"0.20.2" ~compiler_revision:None
               ~configuration
               ~input_locations:(List.map (fun (DEF_aux (_, annot)) -> annot.loc) ast.defs)
               !Jib_compile.representation_specializations
            )
        )
        else None
      in
      ( match (Config.specialization_plan_json, specialization_plan) with
      | Some path, Some plan -> Specialization_plan.write_json path plan
      | _ -> ()
      );
      ( match (Config.specialization_obligations_lean, specialization_plan) with
      | Some path, Some plan -> Specialization_plan.write_lean path plan
      | _ -> ()
      );
      ( match (Config.specialization_obligations_coq, specialization_plan) with
      | Some path, Some plan -> Specialization_plan.write_coq path plan
      | _ -> ()
      );

      let cdefs, ctx, specialization_output_ids, deduplicated_specializations =
        if Config.specialize_c then deduplicate_representation_specializations ctx cdefs
        else (cdefs, ctx, Bindings.empty, 0)
      in
      if deduplicated_specializations > 0 then
        log_phase "deduplicated identical represented specializations=%d" deduplicated_specializations;

      let rec remove_parameters_and_results ctx cdefs removed =
        let cdefs, ctx, removed_now = remove_unused_internal_parameters ctx cdefs specialization_output_ids in
        let cdefs = if !optimize_unit_results then List.map (discard_unread_stack_results ctx) cdefs else cdefs in
        if removed_now = 0 then (cdefs, ctx, removed)
        else remove_parameters_and_results ctx cdefs (removed + removed_now)
      in
      let cdefs, ctx, removed_parameters =
        if Config.optimized_model then remove_parameters_and_results ctx cdefs 0 else (cdefs, ctx, 0)
      in
      if removed_parameters > 0 then log_phase "removed unused internal parameters=%d" removed_parameters;

      generated := IdSet.empty;
      emitted_external_functions := Util.StringSet.empty;
      emitted_external_declarations := Util.StringSet.empty;
      current_static_helper_demands := Util.StringSet.empty;
      static_equality_declarations := [];
      static_equality_declaration_names := Util.StringSet.empty;
      readable_ctyp_names := CTMap.empty;
      readable_ctyp_names_used := Util.StringSet.empty;
      List.iter
        (fun (_, name) -> readable_ctyp_names_used := Util.StringSet.add name !readable_ctyp_names_used)
        Config.c_repr_fixed_bytes_names;
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
            let canonical_file filename = try Unix.realpath filename with Unix.Unix_error (_, _, _) -> filename in
            let same_file left right =
              String.equal left right || String.equal (canonical_file left) (canonical_file right)
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
                (function CDEF_aux (CDEF_type ctype_def, def_annot) -> Some (ctype_def, def_annot) | _ -> None)
                cdefs
            in
            List.iter
              (fun (ctype_def, (def_annot : unit def_annot)) ->
                type_owners := Bindings.add (ctype_def_id ctype_def) (module_index_of_loc def_annot.loc) !type_owners
              )
              type_definitions;
            let type_dependencies ctype_def =
              let contained_ctyps =
                match ctype_def with
                | CTD_enum _ | CTD_abstract _ -> []
                | CTD_abbrev (_, ctyp) -> [ctyp]
                | CTD_struct (_, _, fields) | CTD_variant (_, _, fields) -> List.map snd fields
              in
              List.fold_left (fun ids ctyp -> IdSet.union ids (ctyp_ids ctyp)) IdSet.empty contained_ctyps
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
                (fun dependency owner -> max owner (Option.value ~default:0 (Bindings.find_opt dependency !type_owners)))
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

      (* Analyze all immutable globals together after their final C
         representations and module order are known.  The fixpoint resolves
         aliases even when modular ownership reorders their definitions. *)
      prepare_static_letbinds ctx cdefs;

      (* The register-file member set must be fixed before any definition is
         rendered because [sgen_name] consults it for every reference. *)
      if Config.register_file then (
        match modular_layout with
        | Some (modules, module_index) ->
            prepare_register_file modules module_index cdefs;
            if Config.register_file_thread then prepare_register_file_threading cdefs
        | None -> c_error "--c-register-file requires --c-optimized-model modular output"
      );

      (* Valspecs carry parameter types but not their source names.  Recover
         those names from matching JIB definitions before emitting module
         headers.  Bodyless extern declarations use positional comments:
         clang-tidy can still audit that every parameter is documented, while
         the comment cannot disagree with the linked host definition's actual
         identifier. *)
      function_parameter_names :=
        List.fold_left
          (fun names (CDEF_aux (cdef, _)) ->
            match cdef with
            | CDEF_fundef (id, _, args, _) -> Bindings.add id (List.map sgen_name args) names
            | _ -> names
          )
          Bindings.empty cdefs;

      (* Modular optimized output is emitted in source-module order.  Discover
         demanded host contracts before that streaming pass: a valspec can be
         owned by an early module even when its first call is in a later one.
         The former whole-program document pass happened to collect these
         demands while constructing every function body before filtering the
         declarations; make that dependency explicit instead. *)
      let rec collect_external_calls (I_aux (instr, _)) =
        match instr with
        | I_funcall (_, extern_info, (callee, _), _) ->
            let function_name =
              match extern_info with
              | Extern _ -> string_of_id callee
              | Call _ when ctx_is_extern callee ctx -> ctx_get_extern callee ctx
              | Call _ -> ""
            in
            if function_name <> "" && function_name <> "__sail_fixed_assert" && function_name <> "reg_deref" then
              emitted_external_functions := Util.StringSet.add function_name !emitted_external_functions
        | I_if (_, then_instrs, else_instrs) ->
            List.iter collect_external_calls then_instrs;
            List.iter collect_external_calls else_instrs
        | I_block instrs | I_try_block instrs -> List.iter collect_external_calls instrs
        | _ -> ()
      in
      if Config.optimized_model then
        List.iter
          (function CDEF_aux (CDEF_fundef (_, _, _, instrs), _) -> List.iter collect_external_calls instrs | _ -> ())
          cdefs;

      log_phase "generating C definitions=%d" (List.length cdefs);
      let codegen_with_helper_demands generate =
        current_static_helper_demands := Util.StringSet.empty;
        let docs = generate () in
        (docs, !current_static_helper_demands)
      in
      let should_codegen_optimized_def (CDEF_aux (cdef, _)) =
        match cdef with
        | CDEF_val (id, type_parameters, parameter_types, result_type, extern)
          when Option.is_some extern || ctx_is_extern id ctx ->
            (* Polymorphic and managed-runtime vals are compiler intrinsics,
               not linkable optimized-model ABI symbols.  Their represented
               calls have already been rewritten to concrete helpers (for
               example [eq_bytes32] or fixed-vector access) before emission.
               Retaining the source valspec would either expose unavailable
               [lbits]/[sail_int] types or emit several incompatible C
               declarations for one polymorphic name. *)
            let function_name = match extern with Some name -> name | None -> ctx_get_extern id ctx in
            let compiler_intrinsic =
              (not (Util.list_empty type_parameters))
              || List.exists (ctyp_contains is_managed_ctyp) (result_type :: parameter_types)
              || String.equal function_name "eq_anything"
            in
            if compiler_intrinsic || not (Util.StringSet.mem function_name !emitted_external_functions) then false
            else if Util.StringSet.mem function_name !emitted_external_declarations then false
            else (
              emitted_external_declarations := Util.StringSet.add function_name !emitted_external_declarations;
              true
            )
        | CDEF_val _ -> true
        | _ -> true
      in
      let docs_by_definition =
        if Config.optimized_model then []
        else
          List.map
            (fun cdef ->
              let docs, helper_demands = codegen_with_helper_demands (fun () -> codegen_def ctx cdef) in
              (cdef, docs, helper_demands)
            )
            cdefs
      in
      let definition_docs = List.concat (List.map (fun (_, docs, _) -> docs) docs_by_definition) in
      let model_docs, model_helper_demands =
        if Config.optimized_model then ([], Util.StringSet.empty)
        else codegen_with_helper_demands (fun () -> gen_model_init_fini ctx cdefs)
      in
      let unit_test_docs, unit_test_helper_demands =
        if Config.optimized_model then ([], Util.StringSet.empty)
        else codegen_with_helper_demands (fun () -> gen_unit_test_defs ctx cdefs)
      in
      let docs = definition_docs @ model_docs @ unit_test_docs in
      let docs = if Config.cpp then docs @ gen_constructor_destructor ctx cdefs else docs in

      (* Modular optimized-model output is rendered below, one module at a
         time.  Building the legacy monolithic header and implementation as
         well is both unused by [compile_ast_modules] and retains a second
         whole-program pretty-print tree for large models. *)
      let docs_by_type =
        if Config.optimized_model then
          {
            type_decl = empty;
            func_decl = empty;
            func_def = empty;
            var_decl = empty;
            var_def = empty;
            static_func_def = empty;
          }
        else merge_file_docs docs
      in

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

      let external_type_headers =
        Bindings.fold
          (fun _ header headers -> Util.StringSet.add header headers)
          Config.external_types Util.StringSet.empty
        |> Util.StringSet.elements
      in

      let optimized_base_preamble =
        separate hardline
          ((* Threaded functions declared before the anchor module take a
              pointer to the register file; the parameter type must name one
              file-scope struct rather than a fresh prototype-scoped one. *)
           (if Config.register_file_thread then [ksprintf string "struct %s;" register_file_variable] else [])
          @ [
              string "#include <stdbool.h>";
              string "#include <stddef.h>";
              string "#include <stdint.h>";
              string "#include <stdio.h>";
              string "#include <stdlib.h>";
              string "#include <string.h>";
              string "typedef uint64_t unit;";
              string "#define UNIT UINT64_C(0)";
              string "#define EQUAL(type) eq_ ## type";
              string "#define UNDEFINED(type) undefined_ ## type";
              string "static inline bool eq_unit(void) { return true; }";
              string "static inline bool eq_bool(bool lhs, bool rhs) { return lhs == rhs; }";
              string "static inline bool eq_fbits(uint64_t lhs, uint64_t rhs) { return lhs == rhs; }";
              string "static inline void undefined_unit(void) {}";
              string "static inline bool undefined_bool(void) { return false; }";
              string "static inline uint64_t undefined_fbits(void) { return UINT64_C(0); }";
              string
                "static inline uint64_t safe_rshift(uint64_t value, uint64_t amount) { return amount >= UINT64_C(64) ? \
                 UINT64_C(0) : value >> amount; }";
              string
                "_Noreturn static inline void sail_match_failure(const char *function) { const int write_status = \
                 fprintf(stderr, \"Sail match failure in %s\\n\", function); (void)write_status; abort(); }";
            ]
          )
      in
      let preamble in_header =
        let configured_headers =
          (if in_header then external_type_headers @ Config.header_includes else Config.includes)
          |> List.fold_left (fun headers header -> Util.StringSet.add header headers) Util.StringSet.empty
          |> Util.StringSet.elements
        in
        separate hardline
          (( if Config.optimized_model then (
               match (!requested_modules, in_header) with
               | Some (package, _), true -> [ksprintf string "#include \"%s/spec/abi.h\"" package]
               | _ -> [optimized_base_preamble]
             )
             else if Config.no_lib then []
             else
               [string "#include \"sail.h\""]
               @ (if has_sail_config then [string "#include \"sail_config.h\""] else [])
               @ [string "#include <string.h>"]
           )
          @ (if Config.no_rts then [] else [string "#include \"rts.h\""; string "#include \"elf.h\""])
          @ coverage_include
          @ List.map (fun h -> string (Printf.sprintf "#include \"%s\"" h)) configured_headers
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
        if Config.optimized_model then ""
        else
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
        if Config.optimized_model then ""
        else
          Document.to_string
            (preamble false ^^ hardline
            ^^ Printf.ksprintf string "#include \"%s.h\"" basename
            ^^ hlhl ^^ impl_doc ^^ hlhl
            (* TODO: Does no_rts actually work? Won't actual_main try to call model_main which is missing? *)
            ^^ (if not Config.no_rts then model_pre_exit ^^ hlhl ^^ model_main ^^ hlhl else empty)
            ^^ model_test ^^ hlhl ^^ actual_main ^^ hardline ^^ separate hardline extern_cpp_end ^^ hardline
            )
      in

      ( match (Config.specialization_plan_human, specialization_plan) with
      | Some path, Some plan ->
          Specialization_plan.write_human
            ~backend_symbol:(fun id ->
              sgen_function_id (Option.value ~default:id (Bindings.find_opt id specialization_output_ids))
            )
            path plan
      | _ -> ()
      );
      ( match !requested_modules with
      | None -> ()
      | Some (package, _) ->
          let modules, module_index = Option.get modular_layout in
          let base_header_doc = string "#pragma once" ^^ twice hardline ^^ optimized_base_preamble ^^ hardline in
          let base_header = Document.to_string base_header_doc in
          log_phase "rendered optimized base header bytes=%d" (String.length base_header);
          generated_base_header := Some base_header;
          let include_module stem = ksprintf string "#include \"%s/spec/%s.h\"" package stem in
          let find_required name =
            Array.to_list modules |> List.find_opt (fun (mdl : c_module) -> String.equal mdl.name name)
          in
          let compact_document doc = string (Document.to_string doc) in
          let static_docs = ref [] in
          let demanded_helper_definitions = ref [] in
          let demanded_helper_names = ref Util.StringSet.empty in
          let all_helper_demands = ref Util.StringSet.empty in
          let collect_docs reversed docs =
            List.fold_left
              (fun reversed -> function
                | StaticFunctionDefinition doc ->
                    static_docs := compact_document doc :: !static_docs;
                    reversed
                | DemandedStaticFunctionDefinition (name, doc) ->
                    if not (Util.StringSet.mem name !demanded_helper_names) then (
                      demanded_helper_names := Util.StringSet.add name !demanded_helper_names;
                      demanded_helper_definitions := (name, compact_document doc) :: !demanded_helper_definitions
                    );
                    reversed
                | doc -> doc :: reversed
                )
              reversed docs
          in
          let emitter = Option.get !generated_module_emitter in
          let outputs = ref [] in
          let module_cdefs = Array.make (Array.length modules) [] in
          List.iter
            (fun annotated ->
              let index = module_index annotated in
              module_cdefs.(index) <- annotated :: module_cdefs.(index)
            )
            cdefs;
          Array.iteri (fun index reversed -> module_cdefs.(index) <- List.rev reversed) module_cdefs;
          Array.iteri
            (fun index (mdl : c_module) ->
              let reversed_docs =
                List.fold_left
                  (fun reversed_docs annotated ->
                    if should_codegen_optimized_def annotated then (
                      let generated_docs, helper_demands =
                        codegen_with_helper_demands (fun () -> codegen_def ctx annotated)
                      in
                      all_helper_demands := Util.StringSet.union helper_demands !all_helper_demands;
                      collect_docs reversed_docs generated_docs
                    )
                    else reversed_docs
                  )
                  [] module_cdefs.(index)
              in
              let reversed_docs =
                (* The anchor module declares the model register file after its
                   own definitions: its header transitively includes every
                   earlier module header, so all member field types are
                   complete, and its own declarations precede the
                   compatibility macros. *)
                if Config.register_file && index = !register_file_anchor_index then
                  collect_docs reversed_docs (codegen_register_file_docs ())
                else reversed_docs
              in
              let reversed_docs =
                if index = Array.length modules - 1 then (
                  let generated_model_docs, helper_demands =
                    codegen_with_helper_demands (fun () -> gen_model_init_fini ctx cdefs)
                  in
                  all_helper_demands := Util.StringSet.union helper_demands !all_helper_demands;
                  let reversed_docs = collect_docs reversed_docs generated_model_docs in
                  if Config.cpp then collect_docs reversed_docs (gen_constructor_destructor ctx cdefs)
                  else reversed_docs
                )
                else reversed_docs
              in
              let module_docs = List.rev reversed_docs in
              log_phase "rendering optimized module=%s definitions=%d" mdl.name (List.length module_docs);
              let split = merge_file_docs module_docs in
              let required_headers =
                List.filter_map
                  (fun name ->
                    Option.map (fun (required : c_module) -> include_module required.file_stem) (find_required name)
                  )
                  mdl.requires
              in
              let header_doc =
                string "#pragma once" ^^ twice hardline ^^ separate hardline required_headers
                ^^ (if required_headers = [] then empty else twice hardline)
                ^^ preamble true ^^ twice hardline ^^ split.type_decl ^^ split.func_decl ^^ split.var_decl
                ^^ separate hardline extern_cpp_end ^^ hardline
              in
              let implementation_doc =
                (* Generated code spells register-file members directly as
                   model_registers.NAME; the guard suppresses the header's FFI
                   compatibility macros, which would otherwise rescan the
                   member token (and could capture generated field names). *)
                ( if Config.register_file then ksprintf string "#define %s 1" (register_file_compat_guard ()) ^^ hardline
                  else empty
                )
                ^^ ksprintf string "#include \"%s/spec.h\"" package
                ^^ hardline
                ^^ ksprintf string "#include \"%s/spec/support.h\"" package
                ^^ twice hardline ^^ split.var_def ^^ split.func_def
              in
              let header = Document.to_string header_doc in
              log_phase "rendered optimized module header=%s bytes=%d" mdl.name (String.length header);
              let implementation = Document.to_string implementation_doc in
              log_phase "rendered optimized module implementation=%s bytes=%d" mdl.name (String.length implementation);
              emitter { name = mdl.name; file_stem = mdl.file_stem; header; implementation };
              outputs := { name = mdl.name; file_stem = mdl.file_stem; header = ""; implementation = "" } :: !outputs
            )
            modules;
          let globally_required_static =
            !demanded_helper_definitions |> List.rev
            |> List.filter_map (fun (name, doc) ->
                if Util.StringSet.mem name !all_helper_demands then Some doc else None
            )
            |> separate (twice hardline)
          in
          let static_equality_declarations =
            !static_equality_declarations |> List.rev_map snd |> separate hardline |> fun declarations ->
            if declarations = empty then empty else declarations ^^ twice hardline
          in
          let all_static =
            static_equality_declarations
            ^^ separate (twice hardline) (List.rev !static_docs)
            ^^ globally_required_static
          in
          (* Shared type-support helpers are rendered after all modules have
             reported their demands. Module bodies are emitted immediately,
             so peak memory is bounded by one Sail source module rather than
             the complete generated model. *)
          let support_header_doc =
            string "#pragma once" ^^ twice hardline
            ^^ ksprintf string "#include \"%s/spec.h\"" package
            ^^ twice hardline ^^ all_static ^^ hardline
          in
          let support_header = Document.to_string support_header_doc in
          log_phase "rendered optimized support header bytes=%d" (String.length support_header);
          generated_support_header := Some support_header;
          generated_modules := Some (List.rev !outputs)
      );

      log_phase "complete header-bytes=%d implementation-bytes=%d" (String.length header) (String.length impl);
      (header, impl)
    with Type_error.Type_error (l, err) ->
      c_error ~loc:l ("Unexpected type error when compiling to C:\n" ^ fst (Type_error.string_of_type_error err))

  let compile_ast_modules env effect_info ~package ~emit_module (modules : c_module list) ast =
    if modules = [] then c_error "--c-optimized-model requires a Sail project containing at least one module";
    ( match
        List.find_opt
          (fun (mdl : c_module) -> String.equal mdl.file_stem "support" || String.equal mdl.file_stem "abi")
          modules
      with
    | Some mdl ->
        c_error (Printf.sprintf "Sail module %s maps to the reserved generated file stem '%s'" mdl.name mdl.file_stem)
    | None -> ()
    );
    requested_modules := Some (package, modules);
    generated_modules := None;
    generated_base_header := None;
    generated_support_header := None;
    generated_module_emitter := Some emit_module;
    let _, _ =
      Fun.protect
        ~finally:(fun () ->
          requested_modules := None;
          generated_module_emitter := None
        )
        (fun () -> compile_ast env effect_info package ast)
    in
    match (!generated_modules, !generated_base_header, !generated_support_header) with
    | Some outputs, Some base, Some support ->
        let umbrella =
          "#pragma once\n\n"
          ^ String.concat "\n"
              (List.map (fun output -> Printf.sprintf "#include \"%s/spec/%s.h\"" package output.file_stem) outputs)
          ^ "\n"
        in
        (umbrella, base, support, outputs)
    | _ -> c_error "failed to produce modular optimized-model output"
end
