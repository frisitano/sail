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
let opt_specialization_plan_json = ref None
let opt_specialization_plan_human = ref None
let opt_cpp_class_name = ref "Model"
let opt_cpp_namespace = ref "model"
let opt_cpp_derive_from = ref None

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
    ( Flag.create ~prefix:["c"] "require_bounded_int",
      Arg.Set opt_require_bounded_int,
      "reject arbitrary-precision integers that need a finite semantic Sail bound"
    );
    ( Flag.create ~prefix:["c"] ~arg:"filename" "specialization_plan",
      Arg.String (fun path -> opt_specialization_plan_json := Some path),
      "write a deterministic backend-neutral specialization plan as JSON"
    );
    ( Flag.create ~prefix:["c"] ~arg:"filename" "specialization_plan_human",
      Arg.String (fun path -> opt_specialization_plan_human := Some path),
      "write a human-readable specialization report with descriptive C symbols"
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
  let c_repr_uint64 = ref IdSet.empty in
  let c_repr_int64 = ref IdSet.empty in
  let c_repr_u256 = ref IdSet.empty in
  let c_repr_fixed_bytes = ref Bindings.empty in
  let c_repr_error loc message = raise (Reporting.err_general loc ("C backend: $[c_repr] " ^ message)) in
  let supported_c_repr = ["uint64"; "int64"; "u256"; "fixed_bytes"] in
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
              match (repr, payload) with
              | "uint64", Typ_aux (Typ_id payload_id, _)
                when let payload = string_of_id payload_id in
                     payload = "int" || payload = "nat" ->
                  c_repr_uint64 := IdSet.add id !c_repr_uint64
              | "int64", Typ_aux (Typ_id payload_id, _) when string_of_id payload_id = "int" ->
                  c_repr_int64 := IdSet.add id !c_repr_int64
              | "u256", payload
                when is_bits 256 payload || is_unsigned_range 256 declared_payload || is_unsigned_range 256 payload ->
                  c_repr_u256 := IdSet.add id !c_repr_u256
              | "fixed_bytes", Typ_aux (Typ_app (vector_id, [A_aux (A_nexp length, _); A_aux (A_typ elem_typ, _)]), _)
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
              | "uint64", _ -> c_repr_error attr_loc "uint64 requires a mathematical int or nat payload"
              | "int64", _ -> c_repr_error attr_loc "int64 requires a mathematical int payload"
              | "u256", _ -> c_repr_error attr_loc "u256 requires an exact bits(256) or range(0, 2^256 - 1) payload"
              | "fixed_bytes", _ ->
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
  ( !reserved,
    !overrides,
    !c_repr_uint64,
    !c_repr_int64,
    !c_repr_u256,
    !c_repr_fixed_bytes
  )

let c_target (mode : c_backend_mode) out_file { ast; effect_info; env; default_sail_dir; _ } =
  let reserveds, overrides, c_repr_uint64, c_repr_int64, c_repr_u256, c_repr_fixed_bytes =
    collect_c_name_info ast mode
  in
  let c_repr_uint64 = if !opt_specialize_c then c_repr_uint64 else IdSet.empty in
  let c_repr_int64 = if !opt_specialize_c then c_repr_int64 else IdSet.empty in
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
    let c_repr_uint64 = c_repr_uint64
    let c_repr_int64 = c_repr_int64
    let c_repr_u256 = c_repr_u256
    let c_repr_fixed_bytes = c_repr_fixed_bytes
    let specialize_c = !opt_specialize_c
    let require_bounded_int = !opt_require_bounded_int
    let specialization_plan_json = !opt_specialization_plan_json
    let specialization_plan_human = !opt_specialization_plan_human

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
    (Option.is_some !opt_specialization_plan_json || Option.is_some !opt_specialization_plan_human)
    && not !opt_specialize_c
  then
    raise
      (Reporting.err_general Parse_ast.Unknown
         "C backend: specialization-plan output requires --c-specialize"
      );

  let out_file = Option.value out_file ~default:"out" in
  let basename = Filename.basename out_file in

  let header, impl = Codegen.compile_ast env effect_info basename ast in

  let impl_out = Util.open_output_with_check (out_file ^ "." ^ string_of_mode mode) in
  output_string impl_out.channel impl;
  flush impl_out.channel;
  Util.close_output_with_check impl_out;

  let header_out = Util.open_output_with_check (out_file ^ ".h") in
  output_string header_out.channel header;
  flush header_out.channel;
  Util.close_output_with_check header_out;

  if !opt_build then (
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
    (Target.register ~name:"c" ~options:c_options ~rewrites:(c_cpp_rewrites C) ~supports_abstract_types:true
       ~supports_runtime_config:true (c_target C)
    );
  ignore
    (Target.register ~name:"cpp" ~options:cpp_options ~rewrites:(c_cpp_rewrites Cpp) ~supports_abstract_types:true
       ~supports_runtime_config:true (c_target Cpp)
    )
