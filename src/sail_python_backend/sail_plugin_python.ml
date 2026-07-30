open Libsail

open Ast
open Ast_compare
open Ast_util
open Interactive.State

let opt_runtime_module : string option ref = ref None
let opt_extern_module : string option ref = ref None
let opt_import_files : string list ref = ref []
let opt_preserve_structure = ref false
let opt_split = ref false
let opt_source_root : string option ref = ref None
let opt_pydantic = ref false
let opt_ethereum_fixed_bytes : (string * string) list ref = ref []
let source_val_specs : typ Bindings.t ref = ref Bindings.empty

let valid_module_part value =
  String.length value > 0
  && (match value.[0] with 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false)
  && String.for_all (function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false) value
  && not (List.mem value Python_backend.python_keywords)

let valid_module_name value = List.for_all valid_module_part (String.split_on_char '.' value)

let add_ethereum_fixed_bytes value =
  match String.split_on_char '=' value with
  | [sail_type; python_type] when valid_module_part sail_type && valid_module_part python_type ->
      opt_ethereum_fixed_bytes := !opt_ethereum_fixed_bytes @ [(sail_type, python_type)]
  | _ -> raise (Arg.Bad ("invalid fixed-byte mapping (expected SailType=BytesN): " ^ value))

let python_options =
  [
    ( Flag.create ~prefix:["python"] "split",
      Arg.Set opt_split,
      "emit an importable package split along Sail source-file boundaries"
    );
    ( Flag.create ~prefix:["python"] ~arg:"directory" "source_root",
      Arg.String (fun value -> opt_source_root := Some value),
      "preserve source paths relative to this directory in split packages"
    );
    ( Flag.create ~prefix:["python"] "preserve_structure",
      Arg.Set opt_preserve_structure,
      "prefer source-ordered declarations and direct control flow in Python output"
    );
    ( Flag.create ~prefix:["python"] ~arg:"module" "runtime_module",
      Arg.String
        (fun value ->
          if valid_module_name value then opt_runtime_module := Some value
          else raise (Arg.Bad ("invalid Python module name: " ^ value))
        ),
      "import the Sail runtime from a Python module instead of embedding it"
    );
    ( Flag.create ~prefix:["python"] ~arg:"module" "extern_module",
      Arg.String
        (fun value ->
          if valid_module_name value then opt_extern_module := Some value
          else raise (Arg.Bad ("invalid Python module name: " ^ value))
        ),
      "bind unresolved Sail externs directly to functions in this Python module"
    );
    ( Flag.create ~prefix:["python"] ~arg:"file" "import_file",
      Arg.String (fun file -> opt_import_files := !opt_import_files @ [file]),
      "copy this Python support file into the generated split package (repeatable)"
    );
    ( Flag.create ~prefix:["python"] "pydantic",
      Arg.Set opt_pydantic,
      "emit strict Pydantic dataclasses and runtime validators for constrained Sail records"
    );
    ( Flag.create ~prefix:["python"] ~arg:"SailType=BytesN" "ethereum_fixed_bytes",
      Arg.String add_ethereum_fixed_bytes,
      "map a fixed Sail byte-vector abbreviation to an ethereum-types BytesN class independently of numeric mappings \
       (repeatable)"
    );
  ]

let python_rewrites =
  let open Rewrites in
  [
    ("instantiate_outcomes", [String_arg "python"]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("truncate_hex_literals", []);
    ("mono_rewrites", [If_flag opt_mono_rewrites]);
    ("recheck_defs", [If_flag opt_mono_rewrites]);
    ("toplevel_nexps", [If_mono_arg]);
    ("monomorphise", [String_arg "python"; If_mono_arg]);
    ("atoms_to_singletons", [String_arg "python"; If_mono_arg]);
    ("recheck_defs", [If_mono_arg]);
    ("undefined", [Bool_arg false]);
    ("remove_not_pats", []);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_struct_assignments", []);
    ("exp_lift_assign", []);
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("constant_fold", [String_arg "python"]);
  ]

let output_path = function
  | None -> "out.py"
  | Some path when Filename.check_suffix path ".py" -> path
  | Some path -> path ^ ".py"

let package_path = function
  | None -> "out"
  | Some path when Filename.check_suffix path ".py" -> Filename.chop_suffix path ".py"
  | Some path -> path

let package_name path =
  let name = Filename.basename path in
  if valid_module_part name then name
  else raise (Arg.Bad ("Python split-package directory must have an importable basename: " ^ name))

let rec ensure_directory path =
  if String.equal path "" || String.equal path "." then ()
  else if Sys.file_exists path then (
    if not (Sys.is_directory path) then raise (Arg.Bad ("Python package path is not a directory: " ^ path))
  )
  else (
    ensure_directory (Filename.dirname path);
    Unix.mkdir path 0o755
  )

let write_generated_file package_root ({ Python_backend.relative_path; contents } : Python_backend.generated_file) =
  let path = Filename.concat package_root relative_path in
  ensure_directory (Filename.dirname path);
  let output = Util.open_output_with_check path in
  output_string output.channel contents;
  if String.length contents = 0 || not (Char.equal contents.[String.length contents - 1] '\n') then
    output_char output.channel '\n';
  flush output.channel;
  Util.close_output_with_check output

let imported_python_file path =
  if not (Sys.file_exists path) then raise (Arg.Bad ("Python import file does not exist: " ^ path));
  if Sys.is_directory path then raise (Arg.Bad ("Python import file is a directory: " ^ path));
  let basename = Filename.basename path in
  if not (Filename.check_suffix basename ".py") then
    raise (Arg.Bad ("Python import file must have a .py extension: " ^ path));
  let module_name = Filename.chop_suffix basename ".py" in
  if not (valid_module_part module_name) then
    raise (Arg.Bad ("Python import file must have an importable basename: " ^ basename));
  ({ relative_path = basename; contents = Util.read_whole_file path } : Python_backend.generated_file)

let add_import_files generated =
  let generated_paths =
    List.fold_left
      (fun paths ({ Python_backend.relative_path; _ } : Python_backend.generated_file) ->
        Util.StringSet.add relative_path paths
      )
      Util.StringSet.empty generated
  in
  let imported = List.map imported_python_file !opt_import_files in
  List.iter
    (fun ({ Python_backend.relative_path; _ } : Python_backend.generated_file) ->
      if Util.StringSet.mem relative_path generated_paths then
        raise (Arg.Bad ("Python import file collides with generated package file: " ^ relative_path))
    )
    imported;
  generated @ imported

let preserve_defined_functions (ast : _ Ast_defs.ast) _effect_info _env =
  source_val_specs :=
    List.fold_left
      (fun specs (DEF_aux (definition, _)) ->
        match definition with
        | DEF_val (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (_, typ), _), id, _), _)) -> Bindings.add id typ specs
        | _ -> specs
      )
      Bindings.empty ast.defs;
  let generated_undefined = Python_backend.generated_undefined_function_ids ast.defs in
  let generated_enum_conversions = Python_backend.generated_enum_conversion_function_ids ast.defs in
  let generated_support = IdSet.union generated_undefined generated_enum_conversions in
  let functions =
    List.fold_left
      (fun functions (DEF_aux (definition, _)) ->
        match definition with
        | DEF_fundef fundef when not (IdSet.mem (id_of_fundef fundef) generated_support) ->
            IdSet.add (id_of_fundef fundef) functions
        | DEF_internal_mutrec fundefs ->
            List.fold_left
              (fun functions fundef ->
                if IdSet.mem (id_of_fundef fundef) generated_support then functions
                else IdSet.add (id_of_fundef fundef) functions
              )
              functions fundefs
        | _ -> functions
      )
      IdSet.empty ast.defs
  in
  Specialize.add_initial_calls functions

let python_target out_file { ast; effect_info; env; _ } =
  if !opt_split then (
    let package_root = package_path out_file in
    ensure_directory package_root;
    Python_backend.generate_package ?runtime_module:!opt_runtime_module ?extern_module:!opt_extern_module
      ?source_root:!opt_source_root
      ~preserve_structure:!opt_preserve_structure ~source_val_specs:!source_val_specs
      ~pydantic:!opt_pydantic ~ethereum_fixed_bytes:!opt_ethereum_fixed_bytes
      ~package_name:(package_name package_root) env effect_info ast
    |> add_import_files
    |> List.iter (write_generated_file package_root)
  )
  else (
    if !opt_import_files <> [] then
      raise
        (Reporting.err_general Parse_ast.Unknown
           "--python-import-file requires --python-split so support files have a package destination"
        );
    let generated =
      Python_backend.generate ?runtime_module:!opt_runtime_module ?extern_module:!opt_extern_module
        ~preserve_structure:!opt_preserve_structure
        ~source_val_specs:!source_val_specs ~pydantic:!opt_pydantic
        ~ethereum_fixed_bytes:!opt_ethereum_fixed_bytes env effect_info ast
    in
    let output = Util.open_output_with_check (output_path out_file) in
    output_string output.channel generated;
    output_char output.channel '\n';
    flush output.channel;
    Util.close_output_with_check output
  )

let _ =
  Target.register ~name:"python" ~options:python_options ~pre_rewrites_hook:preserve_defined_functions
    ~rewrites:python_rewrites ~description:"extract executable Python from Sail" python_target
