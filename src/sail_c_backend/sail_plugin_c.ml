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

open Ast_compare
open Ast_util
open Interactive.State

module Big_int = Nat_big_num

let opt_assert_to_exception = ref false
let opt_branch_coverage = ref None
let opt_build = ref false
let opt_generate_header = ref false
let opt_static = ref false
let opt_includes_c : string list ref = ref []
let opt_includes_h : string list ref = ref []
let opt_no_lib = ref false
let opt_no_main = ref false
let opt_no_mangle = ref false
let opt_no_rts = ref false
let opt_preserve_types = ref IdSet.empty
let opt_specialize_c = ref false
let opt_require_bounded_int = ref false
let opt_const_match_tables = ref false
let opt_narrowing_policy : C_backend.narrowing_policy option ref = ref None
let opt_specialization_plan_json = ref None
let opt_specialization_plan_human = ref None
let opt_specialization_obligations_lean = ref None
let opt_specialization_obligations_coq = ref None
let opt_optimized_model = ref false
let opt_register_file = ref false
let opt_register_file_thread = ref false
let opt_register_file_excluded_modules : string list ref = ref []
let opt_register_pins : (string * string) list ref = ref []
let opt_preserved_functions = ref IdSet.empty
let opt_c_optimized_source_root = ref None
let opt_c_optimized_include_dir = ref None
let opt_c_external_types : string Bindings.t ref = ref Bindings.empty
let opt_c_byte_pointer_fields : (Ast.id * Ast.id * string) list ref = ref []
let opt_c_byte_pointer_types : string Bindings.t ref = ref Bindings.empty
let opt_c_package = ref "model"
let opt_c_output_dir = ref None
let opt_cpp_class_name = ref "Model"
let opt_cpp_namespace = ref "model"
let opt_cpp_derive_from = ref None
let input_project = ref None
let direct_byte_pointer_adapter = "__direct"
let input_c_repr_byte_pointer_types = ref IdSet.empty
let input_byte_pointer_signatures : (string option list * string option) Bindings.t ref = ref Bindings.empty
let input_c_repr_fixed_bytes_types : string Bindings.t ref = ref Bindings.empty
let input_fixed_bytes_type_signatures : (Ast.id option list * Ast.id option) Bindings.t ref = ref Bindings.empty

let reset_input_byte_pointer_signatures () =
  input_c_repr_byte_pointer_types := IdSet.empty;
  input_byte_pointer_signatures := Bindings.empty;
  input_c_repr_fixed_bytes_types := Bindings.empty;
  input_fixed_bytes_type_signatures := Bindings.empty

let remember_input_byte_pointer_signatures ast =
  let open Ast in
  let open Ast_defs in
  let open Ast_util in
  let c_repr_name data =
    match attribute_data_string_with_loc data with
    | Some (name, _) -> Some name
    | None -> (
        match data with
        | AD_aux (AD_object fields, _) -> (
            match List.assoc_opt "representation" fields with
            | Some data -> Option.map fst (attribute_data_string_with_loc data)
            | None -> None
          )
        | _ -> None
      )
  in
  input_c_repr_byte_pointer_types :=
    List.fold_left
      (fun types (DEF_aux (def, def_annot)) ->
        match get_def_attribute "c_repr" def_annot with
        | Some (_, Some data) -> (
            match c_repr_name data with
            | Some "byte_pointer" -> (
                match def with
                | DEF_type (TD_aux (TD_variant (id, _, _, _), _)) | DEF_type (TD_aux (TD_abbrev (id, _, _), _)) ->
                    IdSet.add id types
                | _ -> types
              )
            | Some _ | None -> types
          )
        | Some (_, None) | None -> types
      )
      IdSet.empty ast.defs;
  input_c_repr_fixed_bytes_types :=
    List.fold_left
      (fun types (DEF_aux (def, def_annot)) ->
        match get_def_attribute "c_repr" def_annot with
        | Some (_, Some data) -> (
            match (c_repr_name data, def) with
            | ( Some (("fixed_bytes" | "fixed_bytes_u64_lanes") as representation),
                (DEF_type (TD_aux (TD_variant (id, _, _, _), _)) | DEF_type (TD_aux (TD_abbrev (id, _, _), _))) ) ->
                Bindings.add id representation types
            | _ -> types
          )
        | Some (_, None) | None -> types
      )
      !input_c_repr_fixed_bytes_types ast.defs;
  let byte_pointer_adapter (Typ_aux (typ_aux, _)) =
    match typ_aux with
    | Typ_id id -> (
        match Bindings.find_opt id !opt_c_byte_pointer_types with
        | Some _ as adapter -> adapter
        | None when IdSet.mem id !input_c_repr_byte_pointer_types -> Some direct_byte_pointer_adapter
        | None -> None
      )
    | _ -> None
  in
  input_byte_pointer_signatures :=
    List.fold_left
      (fun signatures -> function
        | DEF_aux
            ( DEF_val
                (VS_aux
                   ( VS_val_spec (TypSchm_aux (TypSchm_ts (_, Typ_aux (Typ_fn (arguments, result), _)), _), id, extern),
                     _
                   )
                  ),
              _
            ) ->
            let arguments = List.map byte_pointer_adapter arguments in
            let result = byte_pointer_adapter result in
            if List.exists Option.is_some arguments || Option.is_some result then (
              let signature = (arguments, result) in
              let signatures = Bindings.add id signature signatures in
              match Ast_util.extern_assoc "c" extern with
              | Some external_name -> Bindings.add (mk_id external_name) signature signatures
              | None -> signatures
            )
            else signatures
        | DEF_aux (DEF_let (P_aux (P_typ (typ, pat), _), _), _) -> (
            match (byte_pointer_adapter typ, IdSet.elements (Ast_util.pat_ids pat)) with
            | Some adapter, [id] -> Bindings.add id ([], Some adapter) signatures
            | Some _, _ | None, _ -> signatures
          )
        | _ -> signatures
        )
      !input_byte_pointer_signatures ast.defs;
  let fixed_bytes_alias (Typ_aux (typ_aux, _)) =
    match typ_aux with Typ_id id when Bindings.mem id !input_c_repr_fixed_bytes_types -> Some id | _ -> None
  in
  let rec pattern_arguments (P_aux (pat_aux, _)) =
    match pat_aux with
    | P_typ (Typ_aux (Typ_tuple types, _), P_aux (P_tuple _, _)) -> List.map fixed_bytes_alias types
    | P_typ (typ, _) -> [fixed_bytes_alias typ]
    | P_tuple patterns -> List.concat_map pattern_arguments patterns
    | P_as (pattern, _) | P_var (pattern, _) -> pattern_arguments pattern
    | _ -> [None]
  in
  let clause_signature (FCL_aux (FCL_funcl (id, pexp), _)) =
    let clause_pattern = function
      | Pat_aux (Pat_exp (pattern, _), _) | Pat_aux (Pat_when (pattern, _, _), _) -> pattern
    in
    (id, pattern_arguments (clause_pattern pexp))
  in
  let merge_signature (new_arguments, new_result) = function
    | None -> (new_arguments, new_result)
    | Some (old_arguments, old_result) -> (
        let arguments =
          if List.length old_arguments = List.length new_arguments then
            List.map2 (fun old new_ -> match old with Some _ -> old | None -> new_) old_arguments new_arguments
          else new_arguments
        in
        (arguments, match old_result with Some _ -> old_result | None -> new_result)
      )
  in
  input_fixed_bytes_type_signatures :=
    List.fold_left
      (fun signatures -> function
        | DEF_aux
            ( DEF_val
                (VS_aux
                   ( VS_val_spec (TypSchm_aux (TypSchm_ts (_, Typ_aux (Typ_fn (arguments, result), _)), _), id, extern),
                     _
                   )
                  ),
              _
            ) ->
            let arguments = List.map fixed_bytes_alias arguments in
            let result = fixed_bytes_alias result in
            if List.exists Option.is_some arguments || Option.is_some result then (
              let signature = (arguments, result) in
              let signatures = Bindings.add id signature signatures in
              match Ast_util.extern_assoc "c" extern with
              | Some external_name -> Bindings.add (mk_id external_name) signature signatures
              | None -> signatures
            )
            else signatures
        | DEF_aux
            ( DEF_fundef
                (FD_aux (FD_function (_, Typ_annot_opt_aux (return_annotation, _), (first_clause :: _ as _clauses)), _)),
              _
            ) ->
            let id, arguments = clause_signature first_clause in
            let result =
              match return_annotation with
              | Typ_annot_opt_some (_, typ) -> fixed_bytes_alias typ
              | Typ_annot_opt_none -> None
            in
            if List.exists Option.is_some arguments || Option.is_some result then (
              let signature = merge_signature (arguments, result) (Bindings.find_opt id signatures) in
              Bindings.add id signature signatures
            )
            else signatures
        | DEF_aux (DEF_let (P_aux (P_typ (typ, pat), _), _), _) -> (
            match (fixed_bytes_alias typ, IdSet.elements (Ast_util.pat_ids pat)) with
            | Some alias, [id] -> Bindings.add id ([], Some alias) signatures
            | Some _, _ | None, _ -> signatures
          )
        | _ -> signatures
        )
      !input_fixed_bytes_type_signatures ast.defs

let remember_input_project ast _ env =
  input_project := Type_check.Env.get_modules env;
  (* Splices are applied after the initial-check hook.  Rescan the typed AST so
     optimized-only declarations introduced by a splice retain configured
     byte-pointer argument and result representations. *)
  remember_input_byte_pointer_signatures ast

let c_options =
  [
    (Flag.create ~prefix:["c"] "build", Arg.Set opt_build, "build the generated C/C++ output automatically");
    ( Flag.create ~prefix:["c"] ~arg:"filename" "include",
      Arg.String (fun i -> opt_includes_c := i :: !opt_includes_c),
      "provide additional include for C/C++ implementation output"
    );
    ( Flag.create ~prefix:["c"] ~arg:"filename" "header_include",
      Arg.String (fun i -> opt_includes_h := i :: !opt_includes_h),
      "provide additional include for C/C++ header output"
    );
    (Flag.create ~prefix:["c"] "no_mangle", Arg.Set opt_no_mangle, "produce readable names");
    (Flag.create ~prefix:["c"] "no_main", Arg.Set opt_no_main, "do not generate the main() function");
    (Flag.create ~prefix:["c"] "no_rts", Arg.Set opt_no_rts, "do not include the Sail runtime");
    ( Flag.create ~prefix:["c"] "no_lib",
      Arg.Tuple [Arg.Set opt_no_lib; Arg.Set opt_no_rts],
      "do not include the Sail runtime or library"
    );
    ( Flag.create ~prefix:["c"] ~arg:"prefix" "prefix",
      Arg.String (fun prefix -> C_backend.opt_prefix := prefix),
      "prefix generated C/C++ functions"
    );
    (* This flag is deprecated and will be removed in future. A header is always generated. *)
    (Flag.create ~prefix:["c"] "generate_header", Arg.Set opt_generate_header, "");
    ( Flag.create ~prefix:["c"] ~arg:"parameters" "extra_params",
      Arg.String (fun params -> C_backend.opt_extra_params := Some params),
      "generate C/C++ functions with additional parameters"
    );
    ( Flag.create ~prefix:["c"] ~arg:"arguments" "extra_args",
      Arg.String (fun args -> C_backend.opt_extra_arguments := Some args),
      "supply extra argument to every generated C/C++ function call"
    );
    ( Flag.create ~prefix:["c"] "specialize",
      Arg.Tuple [Arg.Set opt_specialize_c; Arg.Set C_backend.optimize_primops],
      "enable C-only fixed integer representation specialization"
    );
    ( Flag.create ~prefix:["c"] "specialize_log",
      Arg.Set Jib_compile.opt_debug_function_representations,
      "log C representation inference and specialization worklist progress"
    );
    ( Flag.create ~prefix:["c"] ~arg:"count" "specialization_limit",
      Arg.Int
        (fun limit ->
          if limit < 1 then raise (Arg.Bad "--c-specialization-limit must be at least 1")
          else Jib_compile.opt_max_function_specializations := limit
        ),
      "set the maximum proof-backed specializations generated per source function"
    );
    ( Flag.create ~prefix:["c"] "require_bounded_int",
      Arg.Set opt_require_bounded_int,
      "reject arbitrary-precision integers that need a finite semantic Sail bound"
    );
    ( Flag.create ~prefix:["c"] "const_match_tables",
      Arg.Set opt_const_match_tables,
      "lower recovered constant-armed switches into static const table lookups"
    );
    ( Flag.create ~prefix:["c"] "inline_attr",
      Arg.Set C_backend.optimize_inline_attr,
      "inline calls to $[c_inline]-annotated Sail functions in generated C"
    );
    ( Flag.create ~prefix:["c"] "always_inline_attr",
      Arg.Set C_backend.optimize_always_inline_attr,
      "emit C __always_inline__ attributes for $[c_inline]-annotated Sail functions"
    );
    ( Flag.create ~prefix:["c"] "narrowing",
      Arg.Symbol
        ( ["checked"; "proven"; "all"],
          function
          | "checked" -> opt_narrowing_policy := Some C_backend.Narrowing_checked
          | "proven" -> opt_narrowing_policy := Some C_backend.Narrowing_proven
          | "all" -> opt_narrowing_policy := Some C_backend.Narrowing_all
          | _ -> assert false
        ),
      "select checked, proof-backed, or unchecked fixed-integer narrowing"
    );
    ( Flag.create ~prefix:["c"] ~arg:"filename" "specialization_plan",
      Arg.String (fun path -> opt_specialization_plan_json := Some path),
      "write a deterministic backend-neutral specialization plan as JSON"
    );
    ( Flag.create ~prefix:["c"] ~arg:"filename" "specialization_plan_human",
      Arg.String (fun path -> opt_specialization_plan_human := Some path),
      "write a human-readable specialization report with descriptive C symbols"
    );
    ( Flag.create ~prefix:["c"] ~arg:"filename" "specialization_obligations_lean",
      Arg.String (fun path -> opt_specialization_obligations_lean := Some path),
      "write native Lean refinement-obligation definitions"
    );
    ( Flag.create ~prefix:["c"] ~arg:"filename" "specialization_obligations_coq",
      Arg.String (fun path -> opt_specialization_obligations_coq := Some path),
      "write native Coq refinement-obligation definitions"
    );
    ( Flag.create ~prefix:["c"] "optimized_model",
      Arg.Set opt_optimized_model,
      "generate a strict allocation-free specialized C model split by Sail module or source file"
    );
    ( Flag.create ~prefix:["c"] "register_file",
      Arg.Set opt_register_file,
      "emit model registers as members of one 'struct model_registers' so accesses share a single base address \
       (requires --c-optimized-model; generated headers keep per-register compatibility macros for hand-written FFI)"
    );
    ( Flag.create ~prefix:["c"] "register_file_thread",
      Arg.Set opt_register_file_thread,
      "thread a pointer to the model register file through generated functions that access member registers instead of \
       addressing the struct by symbol in every function (requires --c-register-file; entry points called by \
       hand-written FFI keep their signatures)"
    );
    ( Flag.create ~prefix:["c"] ~arg:"module" "register_file_exclude",
      Arg.String
        (fun stem ->
          let stem = String.trim stem in
          if stem = "" then raise (Arg.Bad "--c-register-file-exclude expects a generated module file stem")
          else if List.mem stem !opt_register_file_excluded_modules then
            raise (Arg.Bad ("duplicate --c-register-file-exclude module " ^ stem))
          else opt_register_file_excluded_modules := stem :: !opt_register_file_excluded_modules
        ),
      "keep registers declared in this generated module (by file stem, for example host/debug_enabled) as plain C \
       globals when --c-register-file is enabled"
    );
    ( Flag.create ~prefix:["c"] ~arg:"name=reg[,name=reg]" "register_pin",
      Arg.String
        (fun spec ->
          String.split_on_char ',' spec
          |> List.iter (fun pair ->
              match String.split_on_char '=' (String.trim pair) with
              | [name; machine_register] when String.trim name <> "" && String.trim machine_register <> "" ->
                  let name = String.trim name in
                  if List.mem_assoc name !opt_register_pins then
                    raise (Arg.Bad ("duplicate --c-register-pin register " ^ name))
                  else opt_register_pins := (name, String.trim machine_register) :: !opt_register_pins
              | _ -> raise (Arg.Bad "--c-register-pin expects NAME=MACHINE_REGISTER pairs")
          )
        ),
      "emit the named model registers as global register variables permanently bound to the given machine registers \
       (scalar registers only; the binding is declared in every translation unit and excluded from the register file)"
    );
    ( Flag.create ~prefix:["c"] ~arg:"directory" "optimized_source_root",
      Arg.String (fun directory -> opt_c_optimized_source_root := Some directory),
      "emit optimized-model translation units at paths relative to this Sail source root"
    );
    ( Flag.create ~prefix:["c"] ~arg:"directory" "optimized_include_dir",
      Arg.String (fun directory -> opt_c_optimized_include_dir := Some directory),
      "include root containing externally supplied optimized-model type definitions"
    );
    ( Flag.create ~prefix:["c"] ~arg:"type=header" "optimized_external_type",
      Arg.String
        (fun mapping ->
          match String.index_opt mapping '=' with
          | None -> raise (Arg.Bad "--c-optimized-external-type expects TYPE=HEADER")
          | Some separator ->
              let type_name = String.sub mapping 0 separator |> String.trim in
              let header = String.sub mapping (separator + 1) (String.length mapping - separator - 1) |> String.trim in
              if type_name = "" || header = "" then
                raise (Arg.Bad "--c-optimized-external-type expects non-empty TYPE=HEADER")
              else (
                let id = mk_id type_name in
                if Bindings.mem id !opt_c_external_types then
                  raise (Arg.Bad ("duplicate external optimized-model type " ^ type_name))
                else opt_c_external_types := Bindings.add id header !opt_c_external_types
              )
        ),
      "reuse TYPE from HEADER instead of emitting its C declaration in an optimized-model build"
    );
    ( Flag.create ~prefix:["c"] ~arg:"TYPE.FIELD=ADAPTER" "optimized_byte_pointer_field",
      Arg.String
        (fun mapping ->
          match String.index_opt mapping '=' with
          | None -> raise (Arg.Bad "--c-optimized-byte-pointer-field expects TYPE.FIELD=ADAPTER")
          | Some separator -> (
              let field_name = String.sub mapping 0 separator |> String.trim in
              let adapter = String.sub mapping (separator + 1) (String.length mapping - separator - 1) |> String.trim in
              match String.rindex_opt field_name '.' with
              | None -> raise (Arg.Bad "--c-optimized-byte-pointer-field expects TYPE.FIELD=ADAPTER")
              | Some field_separator ->
                  let type_name = String.sub field_name 0 field_separator |> String.trim in
                  let field =
                    String.sub field_name (field_separator + 1) (String.length field_name - field_separator - 1)
                    |> String.trim
                  in
                  let valid_c_identifier name =
                    let valid_start = function 'A' .. 'Z' | 'a' .. 'z' | '_' -> true | _ -> false in
                    let valid_rest = function 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' -> true | _ -> false in
                    String.length name > 0 && valid_start name.[0] && String.for_all valid_rest name
                  in
                  if type_name = "" || field = "" || not (valid_c_identifier adapter) then
                    raise
                      (Arg.Bad
                         "--c-optimized-byte-pointer-field expects non-empty TYPE.FIELD and a C identifier ADAPTER"
                      )
                  else (
                    let record_id = mk_id type_name in
                    let field_id = mk_id field in
                    if
                      List.exists
                        (fun (configured_record, configured_field, _) ->
                          Id.compare record_id configured_record = 0 && Id.compare field_id configured_field = 0
                        )
                        !opt_c_byte_pointer_fields
                    then raise (Arg.Bad ("duplicate optimized byte-pointer field " ^ field_name))
                    else opt_c_byte_pointer_fields := (record_id, field_id, adapter) :: !opt_c_byte_pointer_fields
                  )
            )
        ),
      "represent integer TYPE.FIELD as uint8_t * and convert semantic offsets with ADAPTER"
    );
    ( Flag.create ~prefix:["c"] ~arg:"TYPE=ADAPTER" "optimized_byte_pointer_type",
      Arg.String
        (fun mapping ->
          match String.index_opt mapping '=' with
          | None -> raise (Arg.Bad "--c-optimized-byte-pointer-type expects TYPE=ADAPTER")
          | Some separator ->
              let type_name = String.sub mapping 0 separator |> String.trim in
              let adapter = String.sub mapping (separator + 1) (String.length mapping - separator - 1) |> String.trim in
              let valid_c_identifier name =
                let valid_start = function 'A' .. 'Z' | 'a' .. 'z' | '_' -> true | _ -> false in
                let valid_rest = function 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' -> true | _ -> false in
                String.length name > 0 && valid_start name.[0] && String.for_all valid_rest name
              in
              if type_name = "" || not (valid_c_identifier adapter) then
                raise (Arg.Bad "--c-optimized-byte-pointer-type expects a non-empty TYPE and a C identifier ADAPTER")
              else (
                let id = mk_id type_name in
                if Bindings.mem id !opt_c_byte_pointer_types then
                  raise (Arg.Bad ("duplicate optimized byte-pointer type " ^ type_name))
                else opt_c_byte_pointer_types := Bindings.add id adapter !opt_c_byte_pointer_types
              )
        ),
      "represent integer TYPE as uint8_t * throughout optimized C and convert semantic offsets with ADAPTER"
    );
    ( Flag.create ~prefix:["c"] ~arg:"package" "package",
      Arg.Set_string opt_c_package,
      "package name used by --c-optimized-model (for example evmsail)"
    );
    ( Flag.create ~prefix:["c"] ~arg:"directory" "output_dir",
      Arg.String (fun directory -> opt_c_output_dir := Some directory),
      "output root used by --c-optimized-model"
    );
    ( Flag.create ~prefix:["c"] "preserve",
      Arg.String
        (fun str ->
          opt_preserved_functions := IdSet.add (mk_id str) !opt_preserved_functions;
          Specialize.add_initial_calls (IdSet.singleton (mk_id str))
        ),
      "make sure the provided function identifier is preserved in C/C++ output"
    );
    (Flag.create ~prefix:["c"] "assert_to_exception", Arg.Set opt_assert_to_exception, "turn assertions into exceptions");
    ( Flag.create ~prefix:["c"] "preserve_type",
      Arg.String (fun str -> opt_preserve_types := IdSet.add (mk_id str) !opt_preserve_types),
      "make sure the provided type identifier is preserved in the C/C++ output"
    );
    ( Flag.create ~prefix:["c"] "fold_unit",
      Arg.String (fun str -> Constant_fold.opt_fold_to_unit := String.split_on_char ',' str),
      "remove comma separated list of functions from C/C++ output, replacing them with unit"
    );
    ( Flag.create ~prefix:["c"] ~arg:"file" "coverage",
      Arg.String (fun str -> opt_branch_coverage := Some (open_out str)),
      "Turn on coverage tracking and output information about all branches and functions to a file"
    );
    ( Flag.create ~prefix:["c"] ~hide_prefix:true "O",
      Arg.Tuple
        [
          Arg.Set C_backend.optimize_primops;
          Arg.Set C_backend.optimize_hoist_allocations;
          Arg.Set Initial_check.opt_fast_undefined;
          Arg.Set C_backend.optimize_alias;
        ],
      "turn on optimizations for C/C++ compilation"
    );
    ( Flag.create ~prefix:["c"] ~hide_prefix:true "Ofixed_int",
      Arg.Set C_backend.optimize_fixed_int,
      "assume fixed size integers rather than GMP arbitrary precision integers"
    );
    ( Flag.create ~prefix:["c"] ~hide_prefix:true "Ofixed_bits",
      Arg.Set C_backend.optimize_fixed_bits,
      "assume fixed size bitvectors rather than arbitrary precision bitvectors"
    );
    (* This flag is deprecated and will be removed in future. *)
    (Flag.create ~prefix:["c"] ~hide_prefix:true "static", Arg.Set opt_static, "");
  ]

(* Additional options when compiling in C++ mode. *)
let cpp_options =
  [
    ( Flag.create ~prefix:["cpp"] ~arg:"identifier" "class_name",
      Arg.String (fun args -> opt_cpp_class_name := args),
      "C++ class name (default 'Model')"
    );
    ( Flag.create ~prefix:["cpp"] ~arg:"identifier" "namespace",
      Arg.String (fun args -> opt_cpp_namespace := args),
      "C++ namespace name (default 'model')"
    );
    ( Flag.create ~prefix:["cpp"] ~arg:"list" "derive_from",
      Arg.String (fun args -> opt_cpp_derive_from := Some args),
      "List of classes/structs to derive the model class from, e.g. 'public foo, private bar'"
    );
  ]

(* The C backend can output in C or C++ mode. *)
type c_backend_mode = C | Cpp

(* Convert the mode to a string. This can be used as the target name and file extension. *)
let string_of_mode = function C -> "c" | Cpp -> "cpp"

let c_cpp_rewrites (mode : c_backend_mode) =
  let target_name = string_of_mode mode in
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg target_name]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("truncate_hex_literals", []);
    ("mono_rewrites", [If_flag opt_mono_rewrites]);
    ("recheck_defs", [If_flag opt_mono_rewrites]);
    ("toplevel_nexps", [If_mono_arg]);
    ("monomorphise", [String_arg target_name; If_mono_arg]);
    ("atoms_to_singletons", [String_arg target_name; If_mono_arg]);
    ("recheck_defs", [If_mono_arg]);
    ("undefined", [Bool_arg false]);
    ("remove_not_pats", []);
    ("pattern_literals_typed", [Literal_arg "all"]);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_struct_assignments", []);
    ("exp_lift_assign", []);
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("constant_fold", [String_arg target_name]);
  ]

(* Find overrides (`$c_override` directive), reserved words
   (`$c_reserved` directive, and extern functions), and validated C
   representation annotations. *)
let collect_c_name_info ast (mode : c_backend_mode) =
  let target_name = string_of_mode mode in
  let open Ast in
  let open Ast_defs in
  let reserved = ref Util.StringSet.empty in
  let overrides = ref Name_generator.Overrides.empty in
  let c_repr_unsigned = ref Bindings.empty in
  let c_repr_signed = ref Bindings.empty in
  let c_repr_u256 = ref IdSet.empty in
  let c_repr_byte_pointer = ref IdSet.empty in
  let c_repr_fixed_bytes = ref Bindings.empty in
  let c_repr_fixed_bytes_u64_lanes = ref Bindings.empty in
  let c_repr_fixed_bytes_u64_lane_alias_lengths = ref [] in
  let c_repr_fixed_bytes_names = ref [] in
  let c_repr_external_names = ref Bindings.empty in
  let c_repr_error loc message = raise (Reporting.err_general loc ("C backend: $[c_repr] " ^ message)) in
  let native_integer_representations =
    [
      ("uint8", (`Unsigned, 8));
      ("uint16", (`Unsigned, 16));
      ("uint32", (`Unsigned, 32));
      ("uint64", (`Unsigned, 64));
      ("int8", (`Signed, 8));
      ("int16", (`Signed, 16));
      ("int32", (`Signed, 32));
      ("int64", (`Signed, 64));
    ]
  in
  let supported_c_repr =
    List.map fst native_integer_representations
    @ ["u256"; "byte_pointer"; "fixed_bytes"; "fixed_bytes_u64_lanes"; "external"]
  in
  let collect_c_repr def def_annot =
    match get_def_attribute "c_repr" def_annot with
    | None -> ()
    | Some (attr_loc, None) -> c_repr_error attr_loc "requires a representation name"
    | Some (attr_loc, Some data) ->
        let repr, repr_loc, c_name =
          match data with
          | AD_aux (AD_string repr, repr_loc) -> (repr, repr_loc, None)
          | AD_aux (AD_object fields, _) ->
              let string_field key =
                match List.assoc_opt key fields with
                | Some data -> (
                    match attribute_data_string_with_loc data with
                    | Some value -> value
                    | None -> c_repr_error attr_loc (Printf.sprintf "%s must be a C identifier" key)
                  )
                | None -> c_repr_error attr_loc (Printf.sprintf "requires a %s field" key)
              in
              let repr, repr_loc = string_field "representation" in
              let name, name_loc = string_field "name" in
              let valid_first = function 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false in
              let valid_rest = function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false in
              if String.length name = 0 || (not (valid_first name.[0])) || not (String.for_all valid_rest name) then
                raise (Reporting.err_general name_loc "C backend: $[c_repr] name must be a C identifier");
              (repr, repr_loc, Some name)
          | _ -> c_repr_error attr_loc "requires a representation name or {representation = ..., name = ...}"
        in
        if not (List.mem repr supported_c_repr) then
          raise
            (Reporting.err_general repr_loc
               (Printf.sprintf "C backend: unsupported representation %S in $[c_repr]; supported representations are %s"
                  repr (String.concat ", " supported_c_repr)
               )
            );
        ( match c_name with
        | Some _ when repr <> "fixed_bytes" && repr <> "fixed_bytes_u64_lanes" && repr <> "external" ->
            c_repr_error attr_loc
              "an explicit name is currently supported only for fixed-byte or external representations"
        | _ -> ()
        );
        if repr = "external" then (
          if !opt_optimized_model then (
            match (c_name, def) with
            | Some name, DEF_type (TD_aux (TD_record (id, _, _, _), _)) ->
                c_repr_external_names := Bindings.add id name !c_repr_external_names
            | None, _ -> c_repr_error attr_loc "external requires an explicit C name"
            | Some _, DEF_type _ -> c_repr_error attr_loc "external is only valid on a struct definition"
            | Some _, _ -> c_repr_error attr_loc "external is only valid on a struct definition"
          )
        )
        else (
          let collect_payload id payload kind ~transparent_alias =
            let declared_payload = payload in
            let payload = Type_check.Env.expand_synonyms def_annot.env payload in
            let is_bits width = function
              | Typ_aux (Typ_app (bits_id, [A_aux (A_nexp (Nexp_aux (Nexp_constant n, _)), _)]), _)
                when string_of_id bits_id = "bitvector" ->
                  Big_int.equal n (Big_int.of_int width)
              | _ -> false
            in
            let is_unsigned_range width = function
              | Typ_aux (Typ_app (range_id, [A_aux (A_nexp low, _); A_aux (A_nexp high, _)]), _)
                when string_of_id range_id = "range" -> (
                  match (Type_check.big_int_of_nexp low, Type_check.big_int_of_nexp high) with
                  | Some low, Some high ->
                      Big_int.equal low Big_int.zero
                      && Big_int.equal high (Big_int.pred (Big_int.pow_int_positive 2 width))
                  | _ -> false
                )
              | _ -> false
            in
            let is_integer_payload = function
              | Typ_aux (Typ_id payload_id, _) ->
                  let payload = string_of_id payload_id in
                  payload = "int" || payload = "nat"
              | Typ_aux (Typ_app (range_id, [_; _]), _) -> string_of_id range_id = "range"
              | _ -> false
            in
            let native_integer_representation = List.assoc_opt repr native_integer_representations in
            match (native_integer_representation, repr, payload) with
            | Some (`Unsigned, width), _, Typ_aux (Typ_id payload_id, _)
              when let payload = string_of_id payload_id in
                   payload = "int" || payload = "nat" ->
                c_repr_unsigned := Bindings.add id width !c_repr_unsigned
            | Some (`Signed, width), _, Typ_aux (Typ_id payload_id, _) when string_of_id payload_id = "int" ->
                c_repr_signed := Bindings.add id width !c_repr_signed
            | None, "u256", payload
              when is_bits 256 payload || is_unsigned_range 256 declared_payload || is_unsigned_range 256 payload ->
                c_repr_u256 := IdSet.add id !c_repr_u256
            | None, "byte_pointer", payload when is_integer_payload payload ->
                c_repr_byte_pointer := IdSet.add id !c_repr_byte_pointer
            | ( None,
                (("fixed_bytes" | "fixed_bytes_u64_lanes") as byte_repr),
                Typ_aux (Typ_app (vector_id, [A_aux (A_nexp length, _); A_aux (A_typ elem_typ, _)]), _) )
              when string_of_id vector_id = "vector" -> (
                let elem_typ = Type_check.Env.expand_synonyms def_annot.env elem_typ in
                if not (is_bits 8 elem_typ || is_unsigned_range 8 elem_typ) then
                  c_repr_error attr_loc
                    (Printf.sprintf "%s requires a vector of byte (bits(8)) elements, but its element type is %s"
                       byte_repr (string_of_typ elem_typ)
                    );
                match nexp_simp length with
                | Nexp_aux (Nexp_constant length, _) when Big_int.less_equal (Big_int.of_int 1) length -> (
                    try
                      let length = Big_int.to_int length in
                      ( match c_name with
                      | Some name -> (
                          let key = (byte_repr, length) in
                          match List.assoc_opt key !c_repr_fixed_bytes_names with
                          | Some existing when existing <> name ->
                              c_repr_error attr_loc
                                (Printf.sprintf
                                   "%s byte width %d already has explicit C name %s (cannot also name it %s)"
                                   byte_repr length existing name
                                )
                          | Some _ -> ()
                          | None -> c_repr_fixed_bytes_names := (key, name) :: !c_repr_fixed_bytes_names
                        )
                      | None -> ()
                      );
                      if byte_repr = "fixed_bytes" then c_repr_fixed_bytes := Bindings.add id length !c_repr_fixed_bytes
                      else (
                        c_repr_fixed_bytes_u64_lanes := Bindings.add id length !c_repr_fixed_bytes_u64_lanes;
                        if transparent_alias then
                          c_repr_fixed_bytes_u64_lane_alias_lengths :=
                            length :: !c_repr_fixed_bytes_u64_lane_alias_lengths
                      )
                    with _ -> c_repr_error attr_loc (byte_repr ^ " length is too large for the C backend")
                  )
                | _ -> c_repr_error attr_loc (byte_repr ^ " requires a statically sized, positive vector payload")
              )
            | Some (`Unsigned, _), _, _ -> c_repr_error attr_loc (repr ^ " requires a mathematical int or nat payload")
            | Some (`Signed, _), _, _ -> c_repr_error attr_loc (repr ^ " requires a mathematical int payload")
            | None, "u256", _ -> c_repr_error attr_loc "u256 requires an exact bits(256) or range(0, 2^256 - 1) payload"
            | None, "byte_pointer", _ ->
                c_repr_error attr_loc "byte_pointer requires a mathematical int, nat, or range payload"
            | None, "fixed_bytes", _ ->
                c_repr_error attr_loc
                  (Printf.sprintf "fixed_bytes requires a statically sized vector of byte elements as its %s" kind)
            | None, "fixed_bytes_u64_lanes", _ ->
                c_repr_error attr_loc
                  (Printf.sprintf "fixed_bytes_u64_lanes requires a statically sized vector of byte elements as its %s"
                     kind
                  )
            | _ -> assert false
          in
          match def with
          | DEF_type (TD_aux (TD_variant (id, [], [Tu_aux (Tu_ty_id (payload, _), _)], true), _)) ->
              collect_payload id payload "payload" ~transparent_alias:false
          | DEF_type (TD_aux (TD_abbrev (id, [], A_aux (A_typ payload, _)), _)) ->
              collect_payload id payload "alias" ~transparent_alias:true
          | DEF_type (TD_aux (TD_variant (_, _, _, false), _)) -> c_repr_error attr_loc "is only valid on a newtype"
          | DEF_type (TD_aux (TD_variant (_, _ :: _, _, true), _)) ->
              c_repr_error attr_loc "does not yet support type parameters"
          | DEF_type (TD_aux (TD_variant (_, [], _, true), _)) ->
              c_repr_error attr_loc "requires exactly one constructor"
          | DEF_type (TD_aux (TD_abbrev (_, _ :: _, _), _)) ->
              c_repr_error attr_loc "does not yet support type parameters"
          | DEF_type _ -> c_repr_error attr_loc "is only valid on a newtype or transparent type alias"
          | _ -> c_repr_error attr_loc "is only valid on a newtype or transparent type alias definition"
        )
  in
  List.iter
    (fun (DEF_aux (def, def_annot)) ->
      collect_c_repr def def_annot;
      match def with
      | DEF_val (VS_aux (VS_val_spec (_, _, extern), _)) -> (
          match extern_assoc target_name extern with
          | Some name -> reserved := Util.StringSet.add name !reserved
          | None -> ()
        )
      | DEF_pragma ("c_reserved", Pragma_line (name, _)) -> reserved := Util.StringSet.add name !reserved
      | DEF_pragma ("c_override", Pragma_structured data) -> (
          match Name_generator.parse_override data with
          | Some (from, target) -> overrides := Name_generator.Overrides.add from target !overrides
          | None -> raise (Reporting.err_general def_annot.loc "Failed to interpret $c_override directive")
        )
      | _ -> ()
    )
    ast.defs;
  ( !reserved,
    !overrides,
    !c_repr_unsigned,
    !c_repr_signed,
    !c_repr_u256,
    !c_repr_byte_pointer,
    !c_repr_fixed_bytes,
    !c_repr_fixed_bytes_u64_lanes,
    List.sort_uniq Int.compare !c_repr_fixed_bytes_u64_lane_alias_lengths,
    List.sort (fun (left, _) (right, _) -> compare left right) !c_repr_fixed_bytes_names,
    !c_repr_external_names
  )

let c_target (mode : c_backend_mode) out_file { ast; effect_info; env; default_sail_dir; _ } =
  if
    ((not (Util.list_empty !opt_c_byte_pointer_fields)) || not (Bindings.is_empty !opt_c_byte_pointer_types))
    && not !opt_optimized_model
  then
    raise (Reporting.err_general Parse_ast.Unknown "optimized byte-pointer representations require --c-optimized-model");
  if not (Bindings.is_empty !opt_c_external_types) then (
    if not !opt_optimized_model then
      raise (Reporting.err_general Parse_ast.Unknown "--c-optimized-external-type requires --c-optimized-model");
    let include_dir =
      match !opt_c_optimized_include_dir with
      | Some directory -> directory
      | None ->
          raise
            (Reporting.err_general Parse_ast.Unknown "--c-optimized-external-type requires --c-optimized-include-dir")
    in
    Bindings.iter
      (fun id header ->
        let escapes_include_root = String.split_on_char '/' header |> List.exists (fun component -> component = "..") in
        if (not (Filename.is_relative header)) || escapes_include_root then
          raise
            (Reporting.err_general Parse_ast.Unknown
               (Printf.sprintf "external optimized-model header for type %s must stay within --c-optimized-include-dir"
                  (string_of_id id)
               )
            );
        if String.exists (fun c -> c = '\n' || c = '\r' || c = '"') header then
          raise
            (Reporting.err_general Parse_ast.Unknown
               (Printf.sprintf "invalid external optimized-model header path for type %s" (string_of_id id))
            );
        let path = Filename.concat include_dir header in
        if not (Sys.file_exists path && not (Sys.is_directory path)) then
          raise
            (Reporting.err_general Parse_ast.Unknown
               (Printf.sprintf "external optimized-model header for type %s does not exist: %s" (string_of_id id) path)
            )
      )
      !opt_c_external_types
  );
  if !opt_optimized_model then (
    match mode with
    | C ->
        opt_specialize_c := true;
        opt_require_bounded_int := true;
        opt_no_main := true;
        opt_no_lib := true;
        opt_no_rts := true;
        opt_no_mangle := true;
        C_backend.optimize_primops := true;
        C_backend.optimize_unit_results := true;
        C_backend.optimize_pure_copies := true;
        C_backend.optimize_dead_letbinds := true
    | Cpp -> raise (Reporting.err_general Parse_ast.Unknown "--c-optimized-model is only supported by the C target")
  );
  if Option.is_some !opt_c_optimized_source_root && not !opt_optimized_model then
    raise (Reporting.err_general Parse_ast.Unknown "--c-optimized-source-root requires --c-optimized-model");
  if !opt_register_file && not !opt_optimized_model then
    raise (Reporting.err_general Parse_ast.Unknown "--c-register-file requires --c-optimized-model");
  if (not (Util.list_empty !opt_register_file_excluded_modules)) && not !opt_register_file then
    raise (Reporting.err_general Parse_ast.Unknown "--c-register-file-exclude requires --c-register-file");
  if !opt_register_file_thread && not !opt_register_file then
    raise (Reporting.err_general Parse_ast.Unknown "--c-register-file-thread requires --c-register-file");
  let ( reserveds,
        overrides,
        c_repr_unsigned,
        c_repr_signed,
        c_repr_u256,
        c_repr_byte_pointer,
        c_repr_fixed_bytes,
        c_repr_fixed_bytes_u64_lanes,
        c_repr_fixed_bytes_u64_lane_alias_lengths,
        c_repr_fixed_bytes_names,
        c_repr_external_names ) =
    collect_c_name_info ast mode
  in
  Bindings.iter
    (fun id _ ->
      if not (Bindings.mem id !opt_c_external_types) then
        raise
          (Reporting.err_general Parse_ast.Unknown
             (Printf.sprintf
                "type %s has $[c_repr {representation = external, ...}] but no --c-optimized-external-type mapping"
                (string_of_id id)
             )
          )
    )
    c_repr_external_names;
  if (not (IdSet.is_empty c_repr_byte_pointer)) && not !opt_optimized_model then
    raise (Reporting.err_general Parse_ast.Unknown "$[c_repr byte_pointer] requires --c-optimized-model");
  let byte_pointer_types =
    IdSet.fold
      (fun id types ->
        if Bindings.mem id types then
          raise
            (Reporting.err_general Parse_ast.Unknown
               (Printf.sprintf "type %s has both $[c_repr byte_pointer] and --c-optimized-byte-pointer-type"
                  (string_of_id id)
               )
            )
        else Bindings.add id direct_byte_pointer_adapter types
      )
      c_repr_byte_pointer !opt_c_byte_pointer_types
  in
  let c_repr_unsigned = if !opt_specialize_c then c_repr_unsigned else Bindings.empty in
  let c_repr_signed = if !opt_specialize_c then c_repr_signed else Bindings.empty in
  let c_repr_u256 = if !opt_specialize_c then c_repr_u256 else IdSet.empty in
  let c_repr_fixed_bytes = if !opt_specialize_c then c_repr_fixed_bytes else Bindings.empty in
  let c_repr_fixed_bytes_u64_lanes = if !opt_specialize_c then c_repr_fixed_bytes_u64_lanes else Bindings.empty in
  let c_repr_fixed_bytes_u64_lane_alias_lengths =
    if !opt_specialize_c then c_repr_fixed_bytes_u64_lane_alias_lengths else []
  in
  let c_repr_fixed_bytes_names = if !opt_specialize_c then c_repr_fixed_bytes_names else [] in
  let c_static_evaluators =
    if !opt_optimized_model then
      let open Ast in
      List.fold_left
        (fun evaluators (DEF_aux (def, def_annot)) ->
          match get_def_attribute "c_static_eval" def_annot with
          | None -> evaluators
          | Some (attr_loc, None) ->
              raise (Reporting.err_general attr_loc "C backend: $[c_static_eval] requires an operation name")
          | Some (attr_loc, Some data) -> (
              match (attribute_data_string_with_loc data, def) with
              | Some ("word_to_fixed_bytes", _), DEF_val (VS_aux (VS_val_spec (_, function_id, extern), _)) -> (
                  let evaluators = Bindings.add function_id "word_to_fixed_bytes" evaluators in
                  match Ast_util.extern_assoc "c" extern with
                  | Some external_name -> Bindings.add (mk_id external_name) "word_to_fixed_bytes" evaluators
                  | None -> evaluators
                )
              | Some (operation, operation_loc), DEF_val _ ->
                  raise
                    (Reporting.err_general operation_loc
                       (Printf.sprintf "C backend: unsupported $[c_static_eval] operation %S" operation)
                    )
              | Some _, _ ->
                  raise (Reporting.err_general attr_loc "C backend: $[c_static_eval] is only valid on a val declaration")
              | None, _ ->
                  raise (Reporting.err_general attr_loc "C backend: $[c_static_eval] operation must be a string")
            )
        )
        Bindings.empty ast.defs
    else Bindings.empty
  in
  let collect_fixed_bytes_signatures representation_name representations =
    let open Ast in
    let input_signatures =
      Bindings.fold
        (fun function_id (arguments, result) signatures ->
          let resolve = function
            | Some alias -> (
                match Bindings.find_opt alias !input_c_repr_fixed_bytes_types with
                | Some name when name = representation_name -> Bindings.find_opt alias representations
                | Some _ | None -> None
              )
            | None -> None
          in
          let arguments = List.map resolve arguments in
          let result = resolve result in
          if List.exists Option.is_some arguments || Option.is_some result then
            Bindings.add function_id (arguments, result) signatures
          else signatures
        )
        !input_fixed_bytes_type_signatures Bindings.empty
    in
    let rec representation_length (Typ_aux (typ_aux, _)) =
      match typ_aux with
      | Typ_id id -> (
          match Bindings.find_opt id representations with
          | Some _ as length -> length
          | None -> (
              match Bindings.find_opt id (Type_check.Env.get_typ_synonyms env) with
              | Some ([], A_aux (A_typ typ, _)) -> representation_length typ
              | _ -> None
            )
        )
      | _ -> None
    in
    List.fold_left
      (fun signatures -> function
        | DEF_aux
            ( DEF_val
                (VS_aux
                   ( VS_val_spec (TypSchm_aux (TypSchm_ts (_, Typ_aux (Typ_fn (arguments, result), _)), _), id, extern),
                     _
                   )
                  ),
              _
            ) ->
            let arguments = List.map representation_length arguments in
            let result = representation_length result in
            if List.exists Option.is_some arguments || Option.is_some result then (
              let signature = (arguments, result) in
              let signatures = Bindings.add id signature signatures in
              match Ast_util.extern_assoc "c" extern with
              | Some external_name -> Bindings.add (mk_id external_name) signature signatures
              | None -> signatures
            )
            else signatures
        | _ -> signatures
        )
      input_signatures ast.defs
  in
  let fixed_bytes_signatures = collect_fixed_bytes_signatures "fixed_bytes" c_repr_fixed_bytes in
  let fixed_bytes_u64_lanes_signatures =
    collect_fixed_bytes_signatures "fixed_bytes_u64_lanes" c_repr_fixed_bytes_u64_lanes
  in
  let narrowing_policy =
    match !opt_narrowing_policy with
    | Some policy -> policy
    | None when !opt_optimized_model -> C_backend.Narrowing_all
    | None when !opt_specialize_c -> C_backend.Narrowing_proven
    | None -> C_backend.Narrowing_checked
  in

  let module Codegen = C_backend.Codegen (struct
    let includes = !opt_includes_c
    let header_includes = !opt_includes_h
    let no_main = !opt_no_main
    let no_lib = !opt_no_lib
    let no_rts = !opt_no_rts
    let no_mangle = !opt_no_mangle

    (* The threaded register-file pointer is a fixed parameter name in
       generated signatures; keep name generation from ever claiming it. *)
    let reserved_words = if !opt_register_file_thread then Util.StringSet.add "regs" reserveds else reserveds
    let overrides = overrides
    let branch_coverage = !opt_branch_coverage
    let assert_to_exception = !opt_assert_to_exception
    let preserve_types = !opt_preserve_types
    let c_repr_unsigned = c_repr_unsigned
    let c_repr_signed = c_repr_signed
    let c_repr_u256 = c_repr_u256
    let c_repr_fixed_bytes = c_repr_fixed_bytes
    let c_repr_fixed_bytes_u64_lanes = c_repr_fixed_bytes_u64_lanes
    let c_repr_fixed_bytes_u64_lane_alias_lengths = c_repr_fixed_bytes_u64_lane_alias_lengths
    let c_repr_fixed_bytes_names = c_repr_fixed_bytes_names
    let c_static_evaluators = c_static_evaluators
    let specialize_c = !opt_specialize_c
    let require_bounded_int = !opt_require_bounded_int
    let const_match_tables = !opt_const_match_tables
    let narrowing_policy = narrowing_policy
    let specialization_plan_json = !opt_specialization_plan_json
    let specialization_plan_human = !opt_specialization_plan_human
    let specialization_obligations_lean = !opt_specialization_obligations_lean
    let specialization_obligations_coq = !opt_specialization_obligations_coq
    let optimized_model = !opt_optimized_model
    let register_file = !opt_register_file
    let register_file_thread = !opt_register_file_thread
    let register_file_excluded_modules = !opt_register_file_excluded_modules
    let register_pins = !opt_register_pins
    let preserved_functions = !opt_preserved_functions
    let external_types = !opt_c_external_types
    let external_type_names = c_repr_external_names
    let byte_pointer_fields = !opt_c_byte_pointer_fields
    let byte_pointer_types = byte_pointer_types
    let byte_pointer_signatures = !input_byte_pointer_signatures
    let fixed_bytes_signatures = fixed_bytes_signatures
    let fixed_bytes_u64_lanes_signatures = fixed_bytes_u64_lanes_signatures
    let package_name = !opt_c_package

    (* TODO: Convert `cpp` to use `c_backend_mode` instead of `bool`. *)
    let cpp = match mode with C -> false | Cpp -> true
    let cpp_class_name = !opt_cpp_class_name
    let cpp_namespace = !opt_cpp_namespace
    let cpp_derive_from = !opt_cpp_derive_from
  end) in
  Reporting.opt_warnings := true;

  if !opt_generate_header then
    Reporting.warn "Deprecated" Parse_ast.Unknown
      "--c-generate-header is deprecated and has no effect; headers are now always generated";

  if !opt_static then
    Reporting.warn "Deprecated" Parse_ast.Unknown "--static is deprecated and no longer has any effect";

  if
    (Option.is_some !opt_specialization_plan_json
    || Option.is_some !opt_specialization_plan_human
    || Option.is_some !opt_specialization_obligations_lean
    || Option.is_some !opt_specialization_obligations_coq
    )
    && not !opt_specialize_c
  then raise (Reporting.err_general Parse_ast.Unknown "C backend: specialization output requires --c-specialize");

  let out_file = Option.value out_file ~default:"out" in
  let basename = Filename.basename out_file in

  let write_file path contents =
    let output = Util.open_output_with_check path in
    output_string output.channel contents;
    flush output.channel;
    Util.close_output_with_check output
  in
  let rec ensure_directory path =
    if path = "" || path = "." || Sys.file_exists path then ()
    else (
      ensure_directory (Filename.dirname path);
      Unix.mkdir path 0o755
    )
  in
  let clean_previous_optimized_outputs include_spec source_spec =
    let rec remove_generated_files suffix directory =
      if Sys.file_exists directory && Sys.is_directory directory then
        Sys.readdir directory
        |> Array.iter (fun entry ->
            let path = Filename.concat directory entry in
            if Sys.is_directory path then remove_generated_files suffix path
            else if Filename.check_suffix entry suffix then Sys.remove path
        )
    in
    remove_generated_files ".h" include_spec;
    remove_generated_files ".c" source_spec;
    let manifest = Filename.concat source_spec "sources.list" in
    if Sys.file_exists manifest then Sys.remove manifest
  in
  let module_file_stem name =
    let buffer = Buffer.create (String.length name) in
    String.iteri
      (fun index c ->
        if Char.uppercase_ascii c = c && Char.lowercase_ascii c <> c && index > 0 then Buffer.add_char buffer '_';
        let c = Char.lowercase_ascii c in
        Buffer.add_char buffer (if (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') then c else '_')
      )
      name;
    Buffer.contents buffer
  in

  let source_file_stem source_root filename =
    let canonical kind path =
      try Unix.realpath path
      with Unix.Unix_error (_, _, _) ->
        raise
          (Reporting.err_general Parse_ast.Unknown (Printf.sprintf "optimized-model %s does not exist: %s" kind path))
    in
    let source_root = canonical "source root" source_root in
    let filename = canonical "source file" filename in
    let root_prefix = source_root ^ Filename.dir_sep in
    if
      String.length filename <= String.length root_prefix
      || String.sub filename 0 (String.length root_prefix) <> root_prefix
    then
      raise
        (Reporting.err_general Parse_ast.Unknown
           (Printf.sprintf "optimized-model source file lies outside --c-optimized-source-root: %s" filename)
        );
    let relative =
      String.sub filename (String.length root_prefix) (String.length filename - String.length root_prefix)
    in
    if not (Filename.check_suffix relative ".sail") then
      raise
        (Reporting.err_general Parse_ast.Unknown
           (Printf.sprintf "optimized-model source file must use the .sail extension: %s" filename)
        );
    let relative = String.sub relative 0 (String.length relative - String.length ".sail") in
    relative |> String.split_on_char '/' |> List.map module_file_stem |> String.concat "/"
  in

  if !opt_optimized_model then (
    let project =
      match !input_project with
      | Some project -> project
      | None ->
          raise
            (Reporting.err_general Parse_ast.Unknown
               "--c-optimized-model requires an input .sail_project so generated files can follow Sail modules"
            )
    in
    let module_name id = fst (Project.module_name project id) in
    let project_modules =
      Project.module_order project
      |> List.map (fun id ->
          let name = module_name id in
          let files = List.map fst (Project.module_files project id) in
          let requires = List.map module_name (Project.module_requires project id) in
          Codegen.{ name; file_stem = module_file_stem name; files; requires }
      )
    in
    let modules =
      match !opt_c_optimized_source_root with
      | None -> project_modules
      | Some source_root ->
          let outputs_by_module : (string, Codegen.c_module list) Hashtbl.t =
            Hashtbl.create (List.length project_modules)
          in
          List.fold_left
            (fun outputs (module_ : Codegen.c_module) ->
              let required_outputs =
                List.filter_map
                  (fun required ->
                    match Hashtbl.find_opt outputs_by_module required with
                    | Some units -> (
                        match List.rev units with [] -> None | unit :: _ -> Some unit.Codegen.name
                      )
                    | None -> None
                  )
                  module_.requires
              in
              let units, _ =
                List.fold_left
                  (fun (units, previous) filename ->
                    let file_stem = source_file_stem source_root filename in
                    let requires = match previous with Some previous -> [previous] | None -> required_outputs in
                    let unit = Codegen.{ name = file_stem; file_stem; files = [filename]; requires } in
                    (unit :: units, Some unit.name)
                  )
                  ([], None) module_.files
              in
              let units = List.rev units in
              Hashtbl.add outputs_by_module module_.name units;
              outputs @ units
            )
            [] project_modules
    in
    let module_names_by_file_stem = Hashtbl.create (List.length modules) in
    List.iter
      (fun (module_ : Codegen.c_module) ->
        match Hashtbl.find_opt module_names_by_file_stem module_.file_stem with
        | Some previous_name ->
            raise
              (Reporting.err_general Parse_ast.Unknown
                 (Printf.sprintf
                    "Optimized C module filename collision: Sail modules %s and %s both map to the file stem '%s'"
                    previous_name module_.name module_.file_stem
                 )
              )
        | None -> Hashtbl.add module_names_by_file_stem module_.file_stem module_.name
      )
      modules;
    let output_root = Option.value !opt_c_output_dir ~default:"ffi/optimized" in
    let include_root = Filename.concat (Filename.concat output_root "include") !opt_c_package in
    let include_spec = Filename.concat include_root "spec" in
    let source_spec = Filename.concat (Filename.concat output_root "src") "spec" in
    ensure_directory include_spec;
    ensure_directory source_spec;
    clean_previous_optimized_outputs include_spec source_spec;
    let emit_module (output : Codegen.c_module_output) =
      let header_path = Filename.concat include_spec (output.file_stem ^ ".h") in
      let source_path = Filename.concat source_spec (output.file_stem ^ ".c") in
      ensure_directory (Filename.dirname header_path);
      ensure_directory (Filename.dirname source_path);
      write_file header_path output.header;
      write_file source_path output.implementation
    in
    let umbrella, base, support, outputs =
      Codegen.compile_ast_modules env effect_info ~package:!opt_c_package ~emit_module modules ast
    in
    write_file (Filename.concat include_root "spec.h") umbrella;
    write_file (Filename.concat include_spec "abi.h") base;
    write_file (Filename.concat include_spec "support.h") support;
    write_file
      (Filename.concat source_spec "sources.list")
      (String.concat "" (List.map (fun (output : Codegen.c_module_output) -> output.file_stem ^ ".c\n") outputs))
  )
  else (
    let header, impl = Codegen.compile_ast env effect_info basename ast in

    write_file (out_file ^ "." ^ string_of_mode mode) impl;
    write_file (out_file ^ ".h") header
  );

  if !opt_build && not !opt_optimized_model then (
    let sail_dir = Reporting.get_sail_dir default_sail_dir in
    let cmd = Printf.sprintf "%s -lgmp -I '%s'/lib '%s'/lib/*.c %s.c -o %s" "gcc" sail_dir sail_dir out_file out_file in
    let _ = Unix.system cmd in
    ()
  )

let _ =
  Pragma.register "c_in_main";
  Pragma.register "c_in_main_post";
  Pragma.register "c_reserved";
  Pragma.register "c_override";
  ignore
    (Target.register ~name:"c" ~options:c_options ~pre_parse_hook:reset_input_byte_pointer_signatures
       ~post_initial_check_hook:remember_input_byte_pointer_signatures ~pre_rewrites_hook:remember_input_project
       ~rewrites:(c_cpp_rewrites C) ~supports_abstract_types:true ~supports_runtime_config:true (c_target C)
    );
  ignore
    (Target.register ~name:"cpp" ~options:cpp_options ~pre_parse_hook:reset_input_byte_pointer_signatures
       ~post_initial_check_hook:remember_input_byte_pointer_signatures ~pre_rewrites_hook:remember_input_project
       ~rewrites:(c_cpp_rewrites Cpp) ~supports_abstract_types:true ~supports_runtime_config:true (c_target Cpp)
    )
