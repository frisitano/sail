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
let opt_optimized_model = ref false
let opt_c_optimized_include_dir = ref None
let opt_c_external_types : string Bindings.t ref = ref Bindings.empty
let opt_c_package = ref "model"
let opt_c_output_dir = ref None
let opt_cpp_class_name = ref "Model"
let opt_cpp_namespace = ref "model"
let opt_cpp_derive_from = ref None
let input_project = ref None

let remember_input_project _ _ env = input_project := Type_check.Env.get_modules env

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
    ( Flag.create ~prefix:["c"] "optimized_model",
      Arg.Set opt_optimized_model,
      "generate a strict allocation-free specialized C model split by Sail module"
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
              let header =
                String.sub mapping (separator + 1) (String.length mapping - separator - 1) |> String.trim
              in
              if type_name = "" || header = "" then
                raise (Arg.Bad "--c-optimized-external-type expects non-empty TYPE=HEADER")
              else
                let id = mk_id type_name in
                if Bindings.mem id !opt_c_external_types then
                  raise (Arg.Bad ("duplicate external optimized-model type " ^ type_name))
                else opt_c_external_types := Bindings.add id header !opt_c_external_types
        ),
      "reuse TYPE from HEADER instead of emitting its C declaration in an optimized-model build"
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
      Arg.String (fun str -> Specialize.add_initial_calls (IdSet.singleton (mk_id str))),
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

(* Find overrides (`$target_name` and legacy `$c_override` directives),
   reserved words (`$c_reserved` directive, and extern functions), and
   validated C representation annotations. *)
let collect_c_name_info ast (mode : c_backend_mode) =
  let target_name = string_of_mode mode in
  let open Ast in
  let open Ast_defs in
  let reserved = ref Util.StringSet.empty in
  let overrides = ref Name_generator.Overrides.empty in
  let c_repr_unsigned = ref Bindings.empty in
  let c_repr_signed = ref Bindings.empty in
  let c_repr_u256 = ref IdSet.empty in
  let c_repr_fixed_bytes = ref Bindings.empty in
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
  let supported_c_repr = List.map fst native_integer_representations @ ["u256"; "fixed_bytes"] in
  let collect_c_repr def def_annot =
    match get_def_attribute "c_repr" def_annot with
    | None -> ()
    | Some (attr_loc, None) -> c_repr_error attr_loc "requires a representation name"
    | Some (attr_loc, Some data) -> (
        match attribute_data_string_with_loc data with
        | None -> c_repr_error attr_loc "requires a representation name"
        | Some (repr, repr_loc) -> (
            if not (List.mem repr supported_c_repr) then
              raise
                (Reporting.err_general repr_loc
                   (Printf.sprintf
                      "C backend: unsupported representation %S in $[c_repr]; supported representations are %s" repr
                      (String.concat ", " supported_c_repr)
                   )
                );
            let collect_payload id payload kind =
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
              | ( None,
                  "fixed_bytes",
                  Typ_aux (Typ_app (vector_id, [A_aux (A_nexp length, _); A_aux (A_typ elem_typ, _)]), _) )
                when string_of_id vector_id = "vector" -> (
                  let elem_typ = Type_check.Env.expand_synonyms def_annot.env elem_typ in
                  if not (is_bits 8 elem_typ) then
                    c_repr_error attr_loc "fixed_bytes requires a vector of byte (bits(8)) elements";
                  match nexp_simp length with
                  | Nexp_aux (Nexp_constant length, _) when Big_int.less_equal (Big_int.of_int 1) length -> (
                      try c_repr_fixed_bytes := Bindings.add id (Big_int.to_int length) !c_repr_fixed_bytes
                      with _ -> c_repr_error attr_loc "fixed_bytes length is too large for the C backend"
                    )
                  | _ -> c_repr_error attr_loc "fixed_bytes requires a statically sized, positive vector payload"
                )
              | Some (`Unsigned, _), _, _ -> c_repr_error attr_loc (repr ^ " requires a mathematical int or nat payload")
              | Some (`Signed, _), _, _ -> c_repr_error attr_loc (repr ^ " requires a mathematical int payload")
              | None, "u256", _ ->
                  c_repr_error attr_loc "u256 requires an exact bits(256) or range(0, 2^256 - 1) payload"
              | None, "fixed_bytes", _ ->
                  c_repr_error attr_loc
                    (Printf.sprintf "fixed_bytes requires a statically sized vector of byte elements as its %s" kind)
              | _ -> assert false
            in
            match def with
            | DEF_type (TD_aux (TD_variant (id, [], [Tu_aux (Tu_ty_id (payload, _), _)], true), _)) ->
                collect_payload id payload "payload"
            | DEF_type (TD_aux (TD_abbrev (id, [], A_aux (A_typ payload, _)), _)) -> collect_payload id payload "alias"
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
      | DEF_pragma ("target_name", Pragma_structured data) -> (
          match Name_generator.parse_target_name data with
          | Some (backend, (from, target)) when backend = target_name ->
              overrides := Name_generator.Overrides.add from target !overrides
          | Some _ -> ()
          | None -> raise (Reporting.err_general def_annot.loc "Failed to interpret $target_name directive")
        )
      | _ -> ()
    )
    ast.defs;
  (!reserved, !overrides, !c_repr_unsigned, !c_repr_signed, !c_repr_u256, !c_repr_fixed_bytes)

let c_target (mode : c_backend_mode) out_file { ast; effect_info; env; default_sail_dir; _ } =
  if not (Bindings.is_empty !opt_c_external_types) then (
    if not !opt_optimized_model then
      raise
        (Reporting.err_general Parse_ast.Unknown
           "--c-optimized-external-type requires --c-optimized-model"
        );
    let include_dir =
      match !opt_c_optimized_include_dir with
      | Some directory -> directory
      | None ->
          raise
            (Reporting.err_general Parse_ast.Unknown
               "--c-optimized-external-type requires --c-optimized-include-dir"
            )
    in
    Bindings.iter
      (fun id header ->
        let escapes_include_root =
          String.split_on_char '/' header |> List.exists (fun component -> component = "..")
        in
        if not (Filename.is_relative header) || escapes_include_root then
          raise
            (Reporting.err_general Parse_ast.Unknown
               (Printf.sprintf
                  "external optimized-model header for type %s must stay within --c-optimized-include-dir"
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
               (Printf.sprintf "external optimized-model header for type %s does not exist: %s"
                  (string_of_id id) path
               )
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
        C_backend.optimize_primops := true
    | Cpp ->
        raise (Reporting.err_general Parse_ast.Unknown "--c-optimized-model is only supported by the C target")
  );
  let reserveds, overrides, c_repr_unsigned, c_repr_signed, c_repr_u256, c_repr_fixed_bytes =
    collect_c_name_info ast mode
  in
  let c_repr_unsigned = if !opt_specialize_c then c_repr_unsigned else Bindings.empty in
  let c_repr_signed = if !opt_specialize_c then c_repr_signed else Bindings.empty in
  let c_repr_u256 = if !opt_specialize_c then c_repr_u256 else IdSet.empty in
  let c_repr_fixed_bytes = if !opt_specialize_c then c_repr_fixed_bytes else Bindings.empty in

  let module Codegen = C_backend.Codegen (struct
    let includes = !opt_includes_c
    let header_includes = !opt_includes_h
    let no_main = !opt_no_main
    let no_lib = !opt_no_lib
    let no_rts = !opt_no_rts
    let no_mangle = !opt_no_mangle
    let reserved_words = reserveds
    let overrides = overrides
    let branch_coverage = !opt_branch_coverage
    let assert_to_exception = !opt_assert_to_exception
    let preserve_types = !opt_preserve_types
    let c_repr_unsigned = c_repr_unsigned
    let c_repr_signed = c_repr_signed
    let c_repr_u256 = c_repr_u256
    let c_repr_fixed_bytes = c_repr_fixed_bytes
    let specialize_c = !opt_specialize_c
    let require_bounded_int = !opt_require_bounded_int
    let optimized_model = !opt_optimized_model
    let external_types = !opt_c_external_types
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
    let modules =
      Project.module_order project
      |> List.map (fun id ->
             let name = module_name id in
             let files = List.map fst (Project.module_files project id) in
             let requires = List.map module_name (Project.module_requires project id) in
             Codegen.{ name; file_stem = module_file_stem name; files; requires }
         )
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
    let umbrella, outputs = Codegen.compile_ast_modules env effect_info ~package:!opt_c_package modules ast in
    write_file (Filename.concat include_root "spec.h") umbrella;
    List.iter
      (fun (output : Codegen.c_module_output) ->
        write_file (Filename.concat include_spec (output.file_stem ^ ".h")) output.header;
        write_file (Filename.concat source_spec (output.file_stem ^ ".c")) output.implementation
      )
      outputs
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
    (Target.register ~name:"c" ~options:c_options ~pre_rewrites_hook:remember_input_project ~rewrites:(c_cpp_rewrites C) ~supports_abstract_types:true
       ~supports_runtime_config:true (c_target C)
    );
  ignore
    (Target.register ~name:"cpp" ~options:cpp_options ~pre_rewrites_hook:remember_input_project ~rewrites:(c_cpp_rewrites Cpp) ~supports_abstract_types:true
       ~supports_runtime_config:true (c_target Cpp)
    )
