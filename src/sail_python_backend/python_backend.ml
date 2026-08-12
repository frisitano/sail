open Libsail

open Ast
open Ast_compare
open Ast_defs
open Ast_util
open Type_check

module Big_int = Nat_big_num
module IntMap = Map.Make (Int)
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let backend_error ?loc:(l = Parse_ast.Unknown) message = raise (Reporting.err_general l ("\nPython backend: " ^ message))

let py_string value = Yojson.Safe.to_string (`String value)
let py_bool = function true -> "True" | false -> "False"

let python_keywords =
  [
    "False";
    "None";
    "True";
    "and";
    "as";
    "assert";
    "async";
    "await";
    "break";
    "class";
    "continue";
    "def";
    "del";
    "elif";
    "else";
    "except";
    "finally";
    "for";
    "from";
    "global";
    "if";
    "import";
    "in";
    "is";
    "lambda";
    "nonlocal";
    "not";
    "or";
    "pass";
    "raise";
    "return";
    "try";
    "while";
    "with";
    "yield";
  ]

let compiler_generated_identifier value =
  let digits_between start finish =
    let rec check index = index >= finish || match value.[index] with '0' .. '9' -> check (index + 1) | _ -> false in
    check start
  in
  let length = String.length value in
  if String.equal value "arg#" then "arg_"
  else if String.equal value "funarg#" then "funarg_"
  else if length > 4 && String.sub value 0 4 = "arg#" && digits_between 4 length then
    "arg_" ^ String.sub value 4 (length - 4)
  else if length > 2 && value.[0] = 'p' && value.[length - 1] = '#' && digits_between 1 (length - 1) then
    String.sub value 0 (length - 1) ^ "_"
  else value

let python_identifier value =
  let value = compiler_generated_identifier value in
  let buffer = Buffer.create (String.length value + 8) in
  String.iteri
    (fun index char ->
      let valid = match char with 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | '0' .. '9' -> index > 0 | _ -> false in
      if valid then Buffer.add_char buffer char else Buffer.add_string buffer (Printf.sprintf "_u%04x_" (Char.code char))
    )
    value;
  let result = if Buffer.length buffer = 0 then "sail_value" else Buffer.contents buffer in
  if List.mem result python_keywords then "sail_" ^ result else result

let extern_binding_name target = "_host_" ^ python_identifier target

let id_string id = string_of_id id
let py_id id = python_identifier (id_string id)

let runtime_names =
  [
    "Any";
    "Annotated";
    "BitWidth";
    "Bits";
    "BoundedUint";
    "Bytes20";
    "Bytes32";
    "Callable";
    "Enum";
    "IntegerRange";
    "ConfigDict";
    "SailError";
    "SailExit";
    "SailMatchFailure";
    "SailReturn";
    "SailThrown";
    "SailUndefinedError";
    "SailUnsupportedError";
    "TypeAlias";
    "U8";
    "U16";
    "U32";
    "U64";
    "U256";
    "Uint";
    "UintEnum";
    "Unsigned";
    "VectorLength";
    "__sail_effects__";
    "__sail_externs__";
    "__sail_functions__";
    "__sail_signatures__";
    "__sail_source_signatures__";
    "__sail_types__";
    "_sail_extern";
    "SailRef";
    "Self";
    "ValidationInfo";
    "bool";
    "call_extern";
    "dataclass";
    "deepcopy";
    "float";
    "finish";
    "field_validator";
    "int";
    "len";
    "list";
    "max";
    "min";
    "object";
    "model_validator";
    "pow";
    "print";
    "pydantic_dataclass";
    "range";
    "register_extern";
    "register_externs";
    "replace";
    "reset";
    "sail_append_64";
    "sail_bitvector";
    "sail_config";
    "sail_cons";
    "sail_constraint";
    "sail_decimal_string_of_int";
    "sail_default";
    "sail_ediv_int";
    "sail_emod_int";
    "sail_hex_string_of_int";
    "sail_pick";
    "sail_pow_int";
    "sail_prerr";
    "sail_prerr_endline";
    "sail_prerr_int";
    "sail_print";
    "sail_print_endline";
    "sail_print_int";
    "sail_range";
    "sail_tdiv_int";
    "sail_tmod_int";
    "sail_undefined";
    "sail_vector_access";
    "sail_vector_append";
    "sail_vector_init";
    "sail_vector_subrange";
    "sail_vector_update";
    "sail_vector_update_subrange";
    "set_sail_config";
    "str";
    "tuple";
    "type";
    "zip";
  ]
  |> StringSet.of_list

let extern_registry_runtime_names = ["call_extern"; "register_extern"; "register_externs"] |> StringSet.of_list

(* Names supplied by [sail_runtime.py], as opposed to Python builtins, support
   imports, or declarations emitted into the generated model itself.  Keeping
   this list explicit at import sites is important: wildcard imports prevent
   Python linters from distinguishing a runtime primitive from an undefined
   generated name. *)
let runtime_import_names ?(external_names = []) () =
  let generated_or_python_names =
    [
      "Any";
      "Annotated";
      "Bytes20";
      "Bytes32";
      "Callable";
      "ConfigDict";
      "Enum";
      "TypeAlias";
      "Self";
      "ValidationInfo";
      "__sail_effects__";
      "__sail_externs__";
      "__sail_functions__";
      "__sail_signatures__";
      "__sail_source_signatures__";
      "__sail_types__";
      "_sail_extern";
      "auto";
      "bool";
      "dataclass";
      "deepcopy";
      "finish";
      "field_validator";
      "float";
      "int";
      "len";
      "list";
      "max";
      "min";
      "model_validator";
      "object";
      "pow";
      "print";
      "pydantic_dataclass";
      "range";
      "replace";
      "reset";
      "str";
      "tuple";
      "type";
      "zip";
    ]
    |> StringSet.of_list
  in
  StringSet.diff runtime_names generated_or_python_names |> fun names ->
  List.fold_left (fun names name -> StringSet.add name names) names external_names |> StringSet.elements

let safe_value_name id =
  let name = py_id id in
  if StringSet.mem name runtime_names then (
    let prefixed = "sail_" ^ name in
    if StringSet.mem prefixed runtime_names then prefixed ^ "_" else prefixed
  )
  else name

(* Every name a generated module binds at its top level: type and constructor
   names, module-level values and registers, imported names, and the runtime
   primitives. Set once per emitted module, before any of its function bodies
   are rendered. *)
let current_module_names : StringSet.t ref = ref StringSet.empty

(* Only function bodies introduce locals, so the dodge set is armed there and
   nowhere else: module-level definitions must keep the very names this set
   records. *)
let module_level_names : StringSet.t ref = ref StringSet.empty

let with_module_level_names names render =
  let previous = !module_level_names in
  module_level_names := names;
  match render () with
  | result ->
      module_level_names := previous;
      result
  | exception exn ->
      module_level_names := previous;
      raise exn

let in_function_body render = with_module_level_names !current_module_names render

(* A Python function has one flat local scope: binding a name anywhere in the
   body makes every read of that name in the body local, including reads the
   backend emits before the binding and reads in the parameter annotations.  A
   local that reused a module-level name therefore hid the module-level
   binding -- for a Sail type alias whose representation constructor the body
   still has to call, that turned into `name(name)` on an ordinary value.
   Locals take a suffixed name instead; module-level references keep theirs. *)
let safe_local_name id =
  let rec dodge candidate =
    if StringSet.mem candidate !module_level_names then dodge (candidate ^ "_") else candidate
  in
  dodge (safe_value_name id)

let add_indent line = if String.equal line "" then line else "    " ^ line
let indent lines = List.map add_indent lines
let block header lines = header :: indent (if lines = [] then ["pass"] else lines)
let concat_map f xs = List.concat (List.map f xs)

let rec bound_id_typs (P_aux (pat_aux, _) as pat) =
  match pat_aux with
  | P_id id -> [(id, typ_of_pat pat)]
  | P_as (inner, id) -> (id, typ_of_pat pat) :: bound_id_typs inner
  | P_typ (_, inner) | P_var (inner, _) -> bound_id_typs inner
  | P_or (left, right) -> bound_id_typs left @ bound_id_typs right
  | P_app (_, pats) | P_vector pats | P_vector_concat pats | P_tuple pats | P_list pats | P_string_append pats ->
      concat_map bound_id_typs pats
  | P_cons (head, tail) -> bound_id_typs head @ bound_id_typs tail
  | P_struct (_, fields, _) -> concat_map (fun (_, field_pat) -> bound_id_typs field_pat) fields
  | P_lit _ | P_wild | P_not _ | P_vector_subrange _ -> []

let bound_ids pat = List.map fst (bound_id_typs pat)

let generated_undefined_function_ids defs =
  List.fold_left
    (fun functions (DEF_aux (definition, def_annot)) ->
      match (definition, get_def_attribute "undefined_gen" def_annot) with
      | DEF_type type_definition, Some (location, Some (AD_aux (AD_string "skip", _))) when is_gen_loc location ->
          IdSet.add (prepend_id "undefined_" (id_of_type_def type_definition)) functions
      | _ -> functions
    )
    IdSet.empty defs

type generated_enum_conversions = {
  to_enum_functions : id Bindings.t;
  from_enum_functions : id Bindings.t;
  numeric_enums : IdSet.t;
  function_ids : IdSet.t;
}

let enum_conversion_names id def_annot =
  let names =
    let open Util.Option_monad in
    let* _, data = get_def_attribute "enum_number_conversions" def_annot in
    let* data = data in
    let* fields = attribute_data_object data in
    let* to_enum, to_location = Option.bind (List.assoc_opt "to_enum" fields) attribute_data_string_with_loc in
    let* from_enum, from_location = Option.bind (List.assoc_opt "from_enum" fields) attribute_data_string_with_loc in
    Some (mk_id ~loc:to_location to_enum, mk_id ~loc:from_location from_enum)
  in
  Option.value names ~default:(append_id id "_of_num", prepend_id "num_of_" id)

let generated_enum_conversion_candidates defs =
  List.fold_left
    (fun candidates (DEF_aux (definition, def_annot)) ->
      match (definition, get_def_attribute "no_enum_number_conversions" def_annot) with
      | DEF_type (TD_aux (TD_enum (id, _, _), _)), Some (location, _) when is_gen_loc location ->
          let to_enum, from_enum = enum_conversion_names id def_annot in
          (to_enum, from_enum, id) :: candidates
      | _ -> candidates
    )
    [] defs

let generated_enum_conversion_function_ids defs =
  let candidates = generated_enum_conversion_candidates defs in
  let candidate_ids =
    List.fold_left
      (fun ids (to_enum, from_enum, _) -> IdSet.add to_enum (IdSet.add from_enum ids))
      IdSet.empty candidates
  in
  List.fold_left
    (fun generated (DEF_aux (definition, def_annot)) ->
      if not (Reporting.is_unknown_loc def_annot.loc) then generated
      else (
        match definition with
        | DEF_val val_spec ->
            let id = id_of_val_spec val_spec in
            if IdSet.mem id candidate_ids then IdSet.add id generated else generated
        | DEF_fundef function_definition ->
            let id = id_of_fundef function_definition in
            if IdSet.mem id candidate_ids then IdSet.add id generated else generated
        | _ -> generated
      )
    )
    IdSet.empty defs

let generated_enum_conversions defs =
  let generated = generated_enum_conversion_function_ids defs in
  List.fold_left
    (fun conversions (to_enum, from_enum, enum_id) ->
      let conversions =
        if IdSet.mem to_enum generated then
          {
            conversions with
            to_enum_functions = Bindings.add to_enum enum_id conversions.to_enum_functions;
            numeric_enums = IdSet.add enum_id conversions.numeric_enums;
            function_ids = IdSet.add to_enum conversions.function_ids;
          }
        else conversions
      in
      if IdSet.mem from_enum generated then
        {
          conversions with
          from_enum_functions = Bindings.add from_enum enum_id conversions.from_enum_functions;
          numeric_enums = IdSet.add enum_id conversions.numeric_enums;
          function_ids = IdSet.add from_enum conversions.function_ids;
        }
      else conversions
    )
    {
      to_enum_functions = Bindings.empty;
      from_enum_functions = Bindings.empty;
      numeric_enums = IdSet.empty;
      function_ids = IdSet.empty;
    }
    (generated_enum_conversion_candidates defs)

let builtin_undefined_function_ids =
  List.fold_left
    (fun functions name -> IdSet.add (mk_id name) functions)
    IdSet.empty
    [
      "undefined_bool";
      "undefined_bit";
      "undefined_int";
      "undefined_nat";
      "undefined_real";
      "undefined_string";
      "undefined_list";
      "undefined_range";
      "undefined_vector";
      "undefined_bitvector";
      "undefined_unit";
    ]

let without_function_definitions functions ast =
  let keep_fundef definition = not (IdSet.mem (id_of_fundef definition) functions) in
  let keep_definition (DEF_aux (definition, def_annot) as original) =
    match definition with
    | DEF_val val_spec when IdSet.mem (id_of_val_spec val_spec) functions -> None
    | DEF_fundef function_definition when not (keep_fundef function_definition) -> None
    | DEF_internal_mutrec function_definitions -> (
        match List.filter keep_fundef function_definitions with
        | [] -> None
        | function_definitions -> Some (DEF_aux (DEF_internal_mutrec function_definitions, def_annot))
      )
    | _ -> Some original
  in
  { ast with defs = List.filter_map keep_definition ast.defs }

let without_generated_undefined_definitions ast =
  without_function_definitions (generated_undefined_function_ids ast.defs) ast

type runtime_numeric_value = { expression : string; already_integer : bool }

type context = {
  env : Env.t;
  val_specs : typ Bindings.t;
  externs : string Bindings.t;
  extern_module : string option;
  functions : IdSet.t;
  records : IdSet.t;
  variants : IdSet.t;
  enums : IdSet.t;
  type_names : string Bindings.t;
  record_quants : typquant Bindings.t;
  record_fields : (id * typ) list Bindings.t;
  record_validity_names : string Bindings.t;
  function_quants : typquant Bindings.t;
  type_aliases : (id * typ) list;
  constructor_names : string Bindings.t;
  enum_members : string Bindings.t;
  registers : IdSet.t;
  top_level_ids : IdSet.t;
  undefined_functions : IdSet.t;
  to_enum_functions : id Bindings.t;
  from_enum_functions : id Bindings.t;
  numeric_enums : IdSet.t;
  type_modules : string list Bindings.t;
  value_modules : string list Bindings.t;
  value_import_names : string Bindings.t StringMap.t;
  register_modules : string list Bindings.t;
  module_import_names : string StringMap.t StringMap.t;
  qualified_type_modules : StringSet.t;
  qualified_value_modules : StringSet.t;
  current_module : string list option;
  qualify_globals : bool;
  pydantic : bool;
  fixed_bytes_types : string IntMap.t;
  mutable current_return_constructor : string option;
  mutable numeric_values : runtime_numeric_value KBindings.t;
  mutable local_ids : IdSet.t;
  mutable referenced_values : IdSet.t;
  mutable referenced_modules : StringSet.t;
  mutable referenced_type_names : StringSet.t;
  mutable next_temp : int;
}

let fresh ctx prefix =
  let index = ctx.next_temp in
  ctx.next_temp <- index + 1;
  Printf.sprintf "_sail_%s_%d" prefix index

let with_local_ids ctx ids render =
  let previous = ctx.local_ids in
  ctx.local_ids <- List.fold_left (fun locals id -> IdSet.add id locals) previous ids;
  match render () with
  | result ->
      ctx.local_ids <- previous;
      result
  | exception exn ->
      ctx.local_ids <- previous;
      raise exn

let binding_name bindings fallback id = Option.value (Bindings.find_opt id bindings) ~default:(fallback id)

let reference_type_name ctx name =
  ctx.referenced_type_names <- StringSet.add name ctx.referenced_type_names;
  name

let same_module left right = List.equal String.equal left right

let module_key components = String.concat "/" (List.map String.lowercase_ascii components)

let module_edge_key source target = module_key source ^ "\x1f" ^ module_key target

let imported_module_name ctx current_module target_module =
  match StringMap.find_opt (module_key current_module) ctx.module_import_names with
  | Some names ->
      Option.value (StringMap.find_opt (module_key target_module) names) ~default:(String.concat "_" target_module)
  | None -> String.concat "_" target_module

let type_name ctx id =
  let name = binding_name ctx.type_names py_id id in
  match ctx.current_module with
  | Some current_module -> (
      match Bindings.find_opt id ctx.type_modules with
      | Some target_module
        when (not (same_module current_module target_module))
             && StringSet.mem (module_edge_key current_module target_module) ctx.qualified_type_modules ->
          ctx.referenced_modules <- StringSet.add (module_key target_module) ctx.referenced_modules;
          imported_module_name ctx current_module target_module ^ "." ^ name
      | _ -> reference_type_name ctx name
    )
  | None -> reference_type_name ctx name
let validity_type_name ctx id =
  reference_type_name ctx (binding_name ctx.record_validity_names (fun id -> py_id id ^ "Validity") id)

let constructor_name ctx id = reference_type_name ctx (binding_name ctx.constructor_names safe_value_name id)

let native_option_constructor env id =
  match Env.union_constructor_info id env with
  | Some (_, _, owner, _) when String.equal (id_string owner) "option" -> (
      match id_string id with "Some" -> Some `Some | "None" -> Some `None | _ -> None
    )
  | _ -> None

let with_referenced_type_names ctx render =
  let previous = ctx.referenced_type_names in
  ctx.referenced_type_names <- StringSet.empty;
  match render () with
  | result ->
      let referenced = ctx.referenced_type_names in
      ctx.referenced_type_names <- previous;
      (result, referenced)
  | exception exn ->
      ctx.referenced_type_names <- previous;
      raise exn

let with_referenced_values ctx render =
  let previous_values = ctx.referenced_values in
  let previous_modules = ctx.referenced_modules in
  ctx.referenced_values <- IdSet.empty;
  ctx.referenced_modules <- StringSet.empty;
  match render () with
  | result ->
      let referenced_values = ctx.referenced_values in
      let referenced_modules = ctx.referenced_modules in
      ctx.referenced_values <- previous_values;
      ctx.referenced_modules <- previous_modules;
      (result, referenced_values, referenced_modules)
  | exception exn ->
      ctx.referenced_values <- previous_values;
      ctx.referenced_modules <- previous_modules;
      raise exn

let value_name ctx id =
  match Bindings.find_opt id ctx.enum_members with
  | Some member ->
      let owner = match String.split_on_char '.' member with owner :: _ -> owner | [] -> member in
      ignore (reference_type_name ctx owner);
      member
  | None -> safe_value_name id

let imported_value_name ctx current_module id =
  match StringMap.find_opt (module_key current_module) ctx.value_import_names with
  | Some names -> binding_name names (value_name ctx) id
  | None -> value_name ctx id

let source_value_name ctx id =
  let name = value_name ctx id in
  if not ctx.qualify_globals then name
  else (
    match ctx.current_module with
    | None -> name
    | Some current_module when IdSet.mem id ctx.registers -> (
        match Bindings.find_opt id ctx.register_modules with
        | Some target_module when same_module current_module target_module -> name
        | Some target_module ->
            ctx.referenced_modules <- StringSet.add (module_key target_module) ctx.referenced_modules;
            imported_module_name ctx current_module target_module ^ "." ^ name
        | None -> name
      )
    | Some current_module when IdSet.mem id ctx.functions || IdSet.mem id ctx.top_level_ids -> (
        match Bindings.find_opt id ctx.value_modules with
        | Some target_module when same_module current_module target_module -> name
        | Some target_module ->
            if StringSet.mem (module_edge_key current_module target_module) ctx.qualified_value_modules then (
              ctx.referenced_modules <- StringSet.add (module_key target_module) ctx.referenced_modules;
              imported_module_name ctx current_module target_module ^ "." ^ name
            )
            else (
              ctx.referenced_values <- IdSet.add id ctx.referenced_values;
              imported_value_name ctx current_module id
            )
        | None -> name
      )
    | Some _ -> name
  )

let val_spec_typs env defs =
  List.fold_left
    (fun specs (DEF_aux (definition, _)) ->
      match definition with
      | DEF_val (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (_, checked_typ), _), id, _), _)) ->
          let typ = try snd (Env.get_val_spec_orig id env) with Type_internal.Type_error _ -> checked_typ in
          Bindings.add id typ specs
      | _ -> specs
    )
    Bindings.empty defs

let merge_source_val_specs checked source =
  Bindings.fold
    (fun id typ specs -> if Bindings.mem id checked then Bindings.add id typ specs else specs)
    source checked

let defined_functions defs =
  List.fold_left
    (fun functions (DEF_aux (definition, _)) ->
      let add_function functions (FD_aux (FD_function (_, _, clauses), _)) =
        match clauses with FCL_aux (FCL_funcl (id, _), _) :: _ -> IdSet.add id functions | [] -> functions
      in
      match definition with
      | DEF_fundef function_definition -> add_function functions function_definition
      | DEF_internal_mutrec definitions -> List.fold_left add_function functions definitions
      | _ -> functions
    )
    IdSet.empty defs

let externs defs =
  let defined = defined_functions defs in
  List.fold_left
    (fun externs (DEF_aux (definition, _)) ->
      match definition with
      | DEF_val (VS_aux (VS_val_spec (_, id, exts), _)) -> (
          match extern_assoc "python" exts with
          | Some name -> Bindings.add id name externs
          | None when not (IdSet.mem id defined) -> Bindings.add id (id_string id) externs
          | None -> externs
        )
      | _ -> externs
    )
    Bindings.empty defs

let choose_name used preferred alternative =
  let rec choose index =
    let candidate = if index = 0 then alternative else Printf.sprintf "%s_%d" alternative index in
    if StringSet.mem candidate !used then choose (index + 1)
    else (
      used := StringSet.add candidate !used;
      candidate
    )
  in
  if not (StringSet.mem preferred !used) then (
    used := StringSet.add preferred !used;
    preferred
  )
  else choose 0

let fixed_bytes_width env typ =
  let constant_int nexp = Option.map Big_int.to_int (big_int_of_nexp nexp) in
  try
    match Env.expand_synonyms env typ with
    | Typ_aux (Typ_app (vector_id, [A_aux (A_nexp length, _); A_aux (A_typ item, _)]), _)
      when id_string vector_id = "vector" -> (
        match (constant_int length, Env.expand_synonyms env item) with
        | Some length, Typ_aux (Typ_app (bits_id, [A_aux (A_nexp width, _)]), _)
          when (id_string bits_id = "bitvector" || id_string bits_id = "bits") && constant_int width = Some 8 ->
            Some length
        | _ -> None
      )
    | _ -> None
  with Type_internal.Type_error _ -> None

let ethereum_bytes_width = function
  | "Bytes0" -> Some 0
  | "Bytes1" -> Some 1
  | "Bytes4" -> Some 4
  | "Bytes8" -> Some 8
  | "Bytes20" -> Some 20
  | "Bytes32" -> Some 32
  | "Bytes48" -> Some 48
  | "Bytes64" -> Some 64
  | "Bytes96" -> Some 96
  | "Bytes256" -> Some 256
  | _ -> None

let fixed_bytes_representations env requested ast =
  let abbreviations =
    List.fold_left
      (fun abbreviations (DEF_aux (definition, _)) ->
        match definition with
        | DEF_type (TD_aux (TD_abbrev (id, _, A_aux (A_typ typ, _)), _)) ->
            StringMap.add (id_string id) typ abbreviations
        | _ -> abbreviations
      )
      StringMap.empty ast.defs
  in
  List.fold_left
    (fun representations (sail_name, python_name) ->
      let typ =
        match StringMap.find_opt sail_name abbreviations with
        | Some typ -> typ
        | None -> backend_error ("--python-ethereum-fixed-bytes names no Sail type abbreviation " ^ sail_name)
      in
      let sail_width =
        match fixed_bytes_width env typ with
        | Some width -> width
        | None ->
            backend_error
              ("--python-ethereum-fixed-bytes requires " ^ sail_name ^ " to expand to a fixed vector of bytes")
      in
      let python_width =
        match ethereum_bytes_width python_name with
        | Some width -> width
        | None -> backend_error ("unsupported ethereum-types fixed-byte class " ^ python_name)
      in
      if sail_width <> python_width then
        backend_error
          (Printf.sprintf "%s expands to %d bytes but %s has width %d" sail_name sail_width python_name python_width);
      match IntMap.find_opt sail_width representations with
      | None -> IntMap.add sail_width python_name representations
      | Some existing when String.equal existing python_name -> representations
      | Some existing ->
          backend_error
            (Printf.sprintf "conflicting Python representations %s and %s for %d-byte Sail vectors" existing python_name
               sail_width
            )
    )
    IntMap.empty requested

let make_context ?(qualify_globals = false) ?(value_modules = Bindings.empty) ?(value_import_names = StringMap.empty)
    ?(register_modules = Bindings.empty) ?(module_import_names = StringMap.empty) ?(source_val_specs = Bindings.empty)
    ?(pydantic = false) ?(ethereum_fixed_bytes = []) ?enum_conversions ?extern_module env ast =
  let enum_conversions = Option.value enum_conversions ~default:(generated_enum_conversions ast.defs) in
  let external_bindings = externs ast.defs in
  let numeric_enums =
    Bindings.fold
      (fun _ enum_id enums -> IdSet.add enum_id enums)
      enum_conversions.to_enum_functions
      (Bindings.fold (fun _ enum_id enums -> IdSet.add enum_id enums) enum_conversions.from_enum_functions IdSet.empty)
  in
  let used =
    ref
      (Bindings.fold
         (fun _ target used -> StringSet.add (extern_binding_name target) used)
         external_bindings runtime_names
      )
  in
  let type_names = ref Bindings.empty in
  let records = ref IdSet.empty in
  let record_quants = ref Bindings.empty in
  let record_fields = ref Bindings.empty in
  let function_quants = ref Bindings.empty in
  let variants = ref IdSet.empty in
  let enums = ref IdSet.empty in
  List.iter
    (fun (DEF_aux (definition, _)) ->
      match definition with
      | DEF_type (TD_aux (type_definition, _)) -> (
          let add_type id set =
            let preferred = py_id id in
            let name = choose_name used preferred (preferred ^ "_type") in
            type_names := Bindings.add id name !type_names;
            set := IdSet.add id !set
          in
          match type_definition with
          | TD_record (id, typq, _, _) -> (
              add_type id records;
              record_quants := Bindings.add id typq !record_quants;
              match type_definition with
              | TD_record (_, _, fields, _) ->
                  record_fields :=
                    Bindings.add id (List.map (fun ((field, typ), _) -> (field, typ)) fields) !record_fields
              | _ -> ()
            )
          | TD_variant (id, _, _, _) -> add_type id variants
          | TD_enum (id, _, _) -> add_type id enums
          | TD_abbrev (id, _, _) | TD_abstract (id, _, _) | TD_bitfield (id, _, _) ->
              let preferred = py_id id in
              let name = choose_name used preferred (preferred ^ "_type") in
              type_names := Bindings.add id name !type_names
        )
      | DEF_val (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, _), _), id, _), _)) ->
          function_quants := Bindings.add id typq !function_quants
      | _ -> ()
    )
    ast.defs;
  let record_validity_names =
    Bindings.fold
      (fun id _ names ->
        let record_name = binding_name !type_names py_id id in
        let preferred = record_name ^ "Validity" in
        Bindings.add id (choose_name used preferred (preferred ^ "_type")) names
      )
      !record_quants Bindings.empty
  in
  let constructor_names = ref Bindings.empty in
  let enum_members = ref Bindings.empty in
  List.iter
    (fun (DEF_aux (definition, _)) ->
      match definition with
      | DEF_type (TD_aux (TD_variant (owner, _, constructors, _), _)) ->
          List.iter
            (fun (Tu_aux (Tu_ty_id (_, id), _)) ->
              let preferred = py_id id in
              let owner_name = binding_name !type_names py_id owner in
              let name = choose_name used preferred (owner_name ^ "_" ^ preferred) in
              constructor_names := Bindings.add id name !constructor_names
            )
            constructors
      | DEF_type (TD_aux (TD_enum (owner, members, _), _)) ->
          let owner_name = binding_name !type_names py_id owner in
          List.iter (fun (id, _) -> enum_members := Bindings.add id (owner_name ^ "." ^ py_id id) !enum_members) members
      | _ -> ()
    )
    ast.defs;
  let registers, top_level_ids =
    List.fold_left
      (fun (registers, lets) (DEF_aux (definition, _)) ->
        match definition with
        | DEF_register (DEC_aux (DEC_reg (_, id, _), _)) -> (IdSet.add id registers, lets)
        | DEF_let (pat, _) -> (registers, List.fold_left (fun lets id -> IdSet.add id lets) lets (bound_ids pat))
        | _ -> (registers, lets)
      )
      (IdSet.empty, IdSet.empty) ast.defs
  in
  let type_aliases =
    List.filter_map
      (fun (DEF_aux (definition, _)) ->
        match definition with
        | DEF_type (TD_aux (TD_abbrev (id, _, A_aux (A_typ typ, _)), _)) -> Some (id, typ)
        | _ -> None
      )
      ast.defs
  in
  {
    env;
    val_specs = merge_source_val_specs (val_spec_typs env ast.defs) source_val_specs;
    externs = external_bindings;
    extern_module;
    functions = defined_functions ast.defs;
    records = !records;
    variants = !variants;
    enums = !enums;
    type_names = !type_names;
    record_quants = !record_quants;
    record_fields = !record_fields;
    record_validity_names;
    function_quants = !function_quants;
    type_aliases;
    constructor_names = !constructor_names;
    enum_members = !enum_members;
    registers;
    top_level_ids;
    undefined_functions = IdSet.union builtin_undefined_function_ids (generated_undefined_function_ids ast.defs);
    to_enum_functions = enum_conversions.to_enum_functions;
    from_enum_functions = enum_conversions.from_enum_functions;
    numeric_enums;
    type_modules = Bindings.empty;
    value_modules;
    value_import_names;
    register_modules;
    module_import_names;
    qualified_type_modules = StringSet.empty;
    qualified_value_modules = StringSet.empty;
    current_module = None;
    qualify_globals;
    pydantic;
    fixed_bytes_types = fixed_bytes_representations env ethereum_fixed_bytes ast;
    current_return_constructor = None;
    numeric_values = KBindings.empty;
    local_ids = IdSet.empty;
    referenced_values = IdSet.empty;
    referenced_modules = StringSet.empty;
    referenced_type_names = StringSet.empty;
    next_temp = 0;
  }

let rec python_nexp = function
  | Nexp_aux (Nexp_id id, _) -> safe_value_name id
  | Nexp_aux (Nexp_var kid, _) ->
      let name = string_of_kid kid in
      python_identifier
        (if String.length name > 0 && name.[0] = '\'' then String.sub name 1 (String.length name - 1) else name)
  | Nexp_aux (Nexp_constant value, _) -> Big_int.to_string value
  | Nexp_aux (Nexp_app (id, [left; right]), _) when id_string id = "div" ->
      "(" ^ python_nexp left ^ " // " ^ python_nexp right ^ ")"
  | Nexp_aux (Nexp_app (id, [left; right]), _) when id_string id = "mod" ->
      "(" ^ python_nexp left ^ " % " ^ python_nexp right ^ ")"
  | Nexp_aux (Nexp_app (id, args), _) -> safe_value_name id ^ "(" ^ String.concat ", " (List.map python_nexp args) ^ ")"
  | Nexp_aux (Nexp_if (_, yes, no), _) -> "(" ^ python_nexp yes ^ " if sail_constraint() else " ^ python_nexp no ^ ")"
  | Nexp_aux (Nexp_times (left, right), _) -> "(" ^ python_nexp left ^ " * " ^ python_nexp right ^ ")"
  | Nexp_aux (Nexp_sum (left, right), _) -> "(" ^ python_nexp left ^ " + " ^ python_nexp right ^ ")"
  | Nexp_aux (Nexp_minus (left, right), _) -> "(" ^ python_nexp left ^ " - " ^ python_nexp right ^ ")"
  | Nexp_aux (Nexp_exp exponent, _) -> "(2 ** " ^ python_nexp exponent ^ ")"
  | Nexp_aux (Nexp_neg value, _) -> "(-" ^ python_nexp value ^ ")"

let const_nexp nexp = Option.map Big_int.to_int (big_int_of_nexp nexp)

let public_uint_width lower upper =
  let exact width =
    Big_int.equal lower Big_int.zero && Big_int.equal upper (Big_int.pred (Big_int.pow_int_positive 2 width))
  in
  List.find_opt exact [8; 16; 32; 64; 256]

let range_annotation _ctx lower upper =
  match (big_int_of_nexp lower, big_int_of_nexp upper) with
  | Some lower_value, Some upper_value when Big_int.less_equal Big_int.zero lower_value -> (
      match public_uint_width lower_value upper_value with
      | Some width -> "U" ^ string_of_int width
      | None -> Printf.sprintf "BoundedUint[%s, %s]" (Big_int.to_string lower_value) (Big_int.to_string upper_value)
    )
  | Some lower_value, None when Big_int.less_equal Big_int.zero lower_value -> "Uint"
  | _ -> "int"

let fixed_bytes_type ctx typ =
  if IntMap.is_empty ctx.fixed_bytes_types then None
  else Option.bind (fixed_bytes_width ctx.env typ) (fun width -> IntMap.find_opt width ctx.fixed_bytes_types)

let aliases_for_typ ctx typ =
  try
    let expanded = Env.expand_synonyms ctx.env typ in
    let source_file = Reporting.loc_file (typ_loc typ) in
    List.filter_map
      (fun (id, alias_typ) ->
        try
          let same_source_file =
            match (source_file, Reporting.loc_file (typ_loc alias_typ)) with
            | Some source_file, Some alias_file -> String.equal source_file alias_file
            | _ -> true
          in
          if same_source_file && Typ.compare (Env.expand_synonyms ctx.env alias_typ) expanded = 0 then Some id else None
        with Type_internal.Type_error _ -> None
      )
      ctx.type_aliases
  with Type_internal.Type_error _ -> []

let named_alias ctx typ = List.fold_left (fun alias id -> Some id) None (aliases_for_typ ctx typ)

let syntactic_named_alias ctx = function
  | (Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, []), _))
    when List.exists (fun (alias, _) -> Id.compare alias id = 0) ctx.type_aliases ->
      Some id
  | _ -> None

let rec python_typ ctx (Typ_aux (typ_aux, _) as typ) =
  match syntactic_named_alias ctx typ with
  | Some id -> type_name ctx id
  | None -> (
      match named_alias ctx typ with
      | Some id -> type_name ctx id
      | None -> (
          match fixed_bytes_type ctx typ with
          | Some python_type -> python_type
          | None -> (
              match typ_aux with
              | Typ_id id -> (
                  match id_string id with
                  | "unit" -> "None"
                  | "bool" -> "bool"
                  | "int" -> "int"
                  | "nat" -> "Uint"
                  | "string" | "string_literal" -> "str"
                  | "real" -> "float"
                  | "bit" -> "Annotated[Bits, BitWidth(1)]"
                  | _ -> type_name ctx id
                )
              | Typ_var _ -> "Any"
              | Typ_fn (args, result) ->
                  "Callable[["
                  ^ String.concat ", " (List.map (python_typ ctx) args)
                  ^ "], " ^ python_typ ctx result ^ "]"
              | Typ_bidir (left, right) -> "tuple[" ^ python_typ ctx left ^ ", " ^ python_typ ctx right ^ "]"
              | Typ_tuple items -> (
                  match items with
                  | [] -> "tuple[()]"
                  | [item] -> "tuple[" ^ python_typ ctx item ^ ",]"
                  | _ -> "tuple[" ^ String.concat ", " (List.map (python_typ ctx) items) ^ "]"
                )
              | Typ_app (id, [A_aux (A_nexp lower, _); A_aux (A_nexp upper, _)]) when id_string id = "range" ->
                  range_annotation ctx lower upper
              | Typ_app (id, [A_aux (A_nexp value, _)]) when id_string id = "atom" || id_string id = "implicit" -> (
                  match big_int_of_nexp value with
                  | Some _ -> "Annotated[int, IntegerRange(" ^ python_nexp value ^ ", " ^ python_nexp value ^ ")]"
                  | None -> "int"
                )
              | Typ_app (id, [A_aux (A_nexp width, _)]) when id_string id = "bitvector" || id_string id = "bits" -> (
                  match big_int_of_nexp width with
                  | Some _ -> "Annotated[Bits, BitWidth(" ^ python_nexp width ^ ")]"
                  | None -> "Bits"
                )
              | Typ_app (id, _) when id_string id = "atom_bool" -> "bool"
              | Typ_app (id, [A_aux (A_nexp value, _)]) when id_string id = "itself" -> (
                  match big_int_of_nexp value with
                  | Some _ -> "Annotated[int, IntegerRange(" ^ python_nexp value ^ ", " ^ python_nexp value ^ ")]"
                  | None -> "int"
                )
              | Typ_app (id, [A_aux (A_nexp length, _); A_aux (A_typ item, _)]) when id_string id = "vector" -> (
                  let items = "list[" ^ python_typ ctx item ^ "]" in
                  match big_int_of_nexp length with
                  | Some _ -> "Annotated[" ^ items ^ ", VectorLength(" ^ python_nexp length ^ ")]"
                  | None -> items
                )
              | Typ_app (id, [A_aux (A_typ item, _)]) when id_string id = "list" -> "list[" ^ python_typ ctx item ^ "]"
              | Typ_app (id, [A_aux (A_typ item, _)]) when id_string id = "option" -> python_typ ctx item ^ " | None"
              | Typ_app (id, [A_aux (A_typ item, _)]) when id_string id = "register" ->
                  "SailRef[" ^ python_typ ctx item ^ "]"
              | Typ_app (id, []) -> python_typ ctx (Typ_aux (Typ_id id, typ_loc typ))
              | Typ_app (id, _) -> type_name ctx id
              | Typ_exist (_, _, body) -> python_typ ctx body
              | Typ_internal_unknown -> "Any"
            )
        )
    )

(* A polymorphic Sail type abbreviation may mention numeric parameters that do
   not exist as Python values at module-import time.  Keep concrete metadata,
   but erase only those free numeric indices from the alias itself. *)
let rec python_alias_typ ctx (Typ_aux (typ_aux, _) as typ) =
  match fixed_bytes_type ctx typ with
  | Some python_type -> python_type
  | None -> (
      match typ_aux with
      | Typ_id id -> (
          match id_string id with
          | "unit" -> "None"
          | "bool" -> "bool"
          | "int" -> "int"
          | "nat" -> "Uint"
          | "string" | "string_literal" -> "str"
          | "real" -> "float"
          | "bit" -> "Annotated[Bits, BitWidth(1)]"
          | _ -> type_name ctx id
        )
      | Typ_var _ -> "Any"
      | Typ_fn (args, result) ->
          "Callable[["
          ^ String.concat ", " (List.map (python_alias_typ ctx) args)
          ^ "], " ^ python_alias_typ ctx result ^ "]"
      | Typ_bidir (left, right) -> "tuple[" ^ python_alias_typ ctx left ^ ", " ^ python_alias_typ ctx right ^ "]"
      | Typ_tuple items -> (
          match items with
          | [] -> "tuple[()]"
          | [item] -> "tuple[" ^ python_alias_typ ctx item ^ ",]"
          | _ -> "tuple[" ^ String.concat ", " (List.map (python_alias_typ ctx) items) ^ "]"
        )
      | Typ_app (id, [A_aux (A_nexp lower, _); A_aux (A_nexp upper, _)]) when id_string id = "range" ->
          range_annotation ctx lower upper
      | Typ_app (id, [A_aux (A_nexp _, _)])
        when id_string id = "atom" || id_string id = "implicit" || id_string id = "itself" ->
          "int"
      | Typ_app (id, [A_aux (A_nexp width, _)]) when id_string id = "bitvector" || id_string id = "bits" -> (
          match big_int_of_nexp width with
          | Some _ -> "Annotated[Bits, BitWidth(" ^ python_nexp width ^ ")]"
          | None -> "Bits"
        )
      | Typ_app (id, _) when id_string id = "atom_bool" -> "bool"
      | Typ_app (id, [A_aux (A_nexp length, _); A_aux (A_typ item, _)]) when id_string id = "vector" -> (
          let items = "list[" ^ python_alias_typ ctx item ^ "]" in
          match big_int_of_nexp length with
          | Some _ -> "Annotated[" ^ items ^ ", VectorLength(" ^ python_nexp length ^ ")]"
          | None -> items
        )
      | Typ_app (id, [A_aux (A_typ item, _)]) when id_string id = "list" -> "list[" ^ python_alias_typ ctx item ^ "]"
      | Typ_app (id, [A_aux (A_typ item, _)]) when id_string id = "option" -> python_alias_typ ctx item ^ " | None"
      | Typ_app (id, [A_aux (A_typ item, _)]) when id_string id = "register" ->
          "SailRef[" ^ python_alias_typ ctx item ^ "]"
      | Typ_app (id, []) -> python_alias_typ ctx (Typ_aux (Typ_id id, typ_loc typ))
      | Typ_app (id, _) -> type_name ctx id
      | Typ_exist (_, _, body) -> python_alias_typ ctx body
      | Typ_internal_unknown -> "Any"
    )

let range_bounds env typ =
  let syntactic = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp lower, _); A_aux (A_nexp upper, _)]), _) when id_string id = "range" -> (
        match (big_int_of_nexp lower, big_int_of_nexp upper) with Some l, Some u -> Some (l, u) | _ -> None
      )
    | _ -> None
  in
  match syntactic typ with
  | Some bounds -> Some bounds
  | None -> (
      try syntactic (Env.expand_synonyms env typ) with Type_internal.Type_error _ -> None
    )

let runtime_integer_atom value = "int(" ^ value ^ ")"

let runtime_numeric_value ?(already_integer = false) expression = { expression; already_integer }

let runtime_integer_value value =
  if value.already_integer then value.expression else runtime_integer_atom value.expression

let rec runtime_nexp ctx = function
  | Nexp_aux (Nexp_id id, _) -> Some (runtime_integer_atom (source_value_name ctx id))
  | Nexp_aux (Nexp_var kid, _) -> Option.map runtime_integer_value (KBindings.find_opt kid ctx.numeric_values)
  | Nexp_aux (Nexp_constant value, _) -> Some (Big_int.to_string value)
  | Nexp_aux (Nexp_app (id, args), _) ->
      let args = List.map (runtime_nexp ctx) args in
      if List.for_all Option.is_some args then (
        let args = List.map Option.get args in
        Some
          ( match (id_string id, args) with
          | "div", [left; right] -> "(" ^ left ^ " // " ^ right ^ ")"
          | "mod", [left; right] -> "(" ^ left ^ " % " ^ right ^ ")"
          | _ -> safe_value_name id ^ "(" ^ String.concat ", " args ^ ")"
          )
      )
      else None
  | Nexp_aux (Nexp_if (condition, yes, no), _) ->
      Option.bind (runtime_constraint ctx condition) (fun condition ->
          Option.bind (runtime_nexp ctx yes) (fun yes ->
              Option.map (fun no -> "(" ^ yes ^ " if " ^ condition ^ " else " ^ no ^ ")") (runtime_nexp ctx no)
          )
      )
  | Nexp_aux (Nexp_times (left, right), _) ->
      Option.bind (runtime_nexp ctx left) (fun left ->
          Option.map (fun right -> "(" ^ left ^ " * " ^ right ^ ")") (runtime_nexp ctx right)
      )
  | Nexp_aux (Nexp_sum (left, right), _) ->
      Option.bind (runtime_nexp ctx left) (fun left ->
          Option.map (fun right -> "(" ^ left ^ " + " ^ right ^ ")") (runtime_nexp ctx right)
      )
  | Nexp_aux (Nexp_minus (left, right), _) ->
      Option.bind (runtime_nexp ctx left) (fun left ->
          Option.map (fun right -> "(" ^ left ^ " - " ^ right ^ ")") (runtime_nexp ctx right)
      )
  | Nexp_aux (Nexp_exp exponent, _) -> Option.map (fun exponent -> "(2 ** " ^ exponent ^ ")") (runtime_nexp ctx exponent)
  | Nexp_aux (Nexp_neg value, _) -> Option.map (fun value -> "(-" ^ value ^ ")") (runtime_nexp ctx value)

and runtime_constraint ctx (NC_aux (constraint_aux, _)) =
  let binary_nexp operator left right =
    Option.bind (runtime_nexp ctx left) (fun left ->
        Option.map (fun right -> "(" ^ left ^ " " ^ operator ^ " " ^ right ^ ")") (runtime_nexp ctx right)
    )
  in
  let binary_constraint operator left right =
    Option.bind (runtime_constraint ctx left) (fun left ->
        Option.map (fun right -> "(" ^ left ^ " " ^ operator ^ " " ^ right ^ ")") (runtime_constraint ctx right)
    )
  in
  match constraint_aux with
  | NC_equal (left, right) ->
      Option.bind (runtime_typ_arg ctx left) (fun left ->
          Option.map (fun right -> "(" ^ left ^ " == " ^ right ^ ")") (runtime_typ_arg ctx right)
      )
  | NC_not_equal (left, right) ->
      Option.bind (runtime_typ_arg ctx left) (fun left ->
          Option.map (fun right -> "(" ^ left ^ " != " ^ right ^ ")") (runtime_typ_arg ctx right)
      )
  | NC_ge (left, right) -> binary_nexp ">=" left right
  | NC_gt (left, right) -> binary_nexp ">" left right
  | NC_le (left, right) -> binary_nexp "<=" left right
  | NC_lt (left, right) -> binary_nexp "<" left right
  | NC_set (value, members) ->
      Option.map
        (fun value -> value ^ " in {" ^ String.concat ", " (List.map Nat_big_num.to_string members) ^ "}")
        (runtime_nexp ctx value)
  | NC_or (left, right) -> binary_constraint "or" left right
  | NC_and (left, right) -> binary_constraint "and" left right
  | NC_app (id, args) ->
      let args = List.map (runtime_typ_arg ctx) args in
      if List.for_all Option.is_some args then
        Some (source_value_name ctx id ^ "(" ^ String.concat ", " (List.map Option.get args) ^ ")")
      else None
  | NC_id id -> Some (source_value_name ctx id)
  | NC_var kid -> Option.map (fun value -> value.expression) (KBindings.find_opt kid ctx.numeric_values)
  | NC_true -> Some "True"
  | NC_false -> Some "False"

and runtime_typ_arg ctx (A_aux (arg, _)) =
  match arg with A_nexp nexp -> runtime_nexp ctx nexp | A_bool nc -> runtime_constraint ctx nc | A_typ _ -> None

let required_runtime_nexp ~loc ctx purpose nexp =
  match runtime_nexp ctx nexp with
  | Some value -> value
  | None -> backend_error ~loc ("cannot recover runtime value for polymorphic " ^ purpose ^ " " ^ string_of_nexp nexp)

let required_runtime_constraint ~loc ctx env purpose constraint_ =
  let constraint_ = Env.expand_constraint_synonyms env constraint_ in
  match runtime_constraint ctx constraint_ with
  | Some value -> value
  | None ->
      backend_error ~loc
        ("cannot recover runtime values needed to validate " ^ purpose ^ " constraint "
       ^ string_of_n_constraint constraint_
        )

let with_numeric_values ctx values render =
  let previous = ctx.numeric_values in
  ctx.numeric_values <- values;
  match render () with
  | result ->
      ctx.numeric_values <- previous;
      result
  | exception exn ->
      ctx.numeric_values <- previous;
      raise exn

let kid_name kid =
  let name = string_of_kid kid in
  python_identifier
    (if String.length name > 0 && Char.equal name.[0] '\'' then String.sub name 1 (String.length name - 1) else name)

let runtime_quantifiers typq =
  List.filter_map
    (function
      | QI_aux (QI_id (KOpt_aux (KOpt_kind (K_aux (K_int, _), kid), _)), _) -> Some (kid, kid_name kid, "int")
      | QI_aux (QI_id (KOpt_aux (KOpt_kind (K_aux (K_bool, _), kid), _)), _) -> Some (kid, kid_name kid, "bool")
      | QI_aux (QI_id (KOpt_aux (KOpt_kind (K_aux (K_type, _), _), _)), _) | QI_aux (QI_constraint _, _) -> None
      )
    typq

let typquant_constraints typq =
  List.filter_map (function QI_aux (QI_constraint constraint_, _) -> Some constraint_ | _ -> None) typq

let record_has_validity ctx typq = ctx.pydantic && runtime_quantifiers typq <> []

let decimal_integer_literal value =
  let length = String.length value in
  let digits_from start =
    start < length
    &&
    let rec digits index = index = length || match value.[index] with '0' .. '9' -> digits (index + 1) | _ -> false in
    digits start
  in
  digits_from 0 || (length > 1 && Char.equal value.[0] '-' && digits_from 1)

let representation_class ctx env typ =
  match fixed_bytes_type ctx typ with
  | Some python_type -> Some python_type
  | None -> (
      let expanded = Env.expand_synonyms env typ in
      let syntactic_alias = syntactic_named_alias ctx typ in
      match expanded with
      | Typ_aux (Typ_app (id, [A_aux (A_nexp lower, _); A_aux (A_nexp upper, _)]), _) when id_string id = "range" -> (
          match big_int_of_nexp lower with
          | Some lower when Big_int.less_equal Big_int.zero lower -> (
              match syntactic_alias with
              | Some alias -> Some (type_name ctx alias)
              | None -> (
                  match named_alias ctx typ with
                  | Some alias -> Some (type_name ctx alias)
                  | None -> (
                      match big_int_of_nexp upper with
                      | Some upper -> (
                          match public_uint_width lower upper with
                          | Some width -> Some ("U" ^ string_of_int width)
                          | None ->
                              Some
                                (Printf.sprintf "BoundedUint[%s, %s]" (Big_int.to_string lower) (Big_int.to_string upper)
                                )
                        )
                      | None -> Some "Uint"
                    )
                )
            )
          | _ -> None
        )
      | _ -> (
          match expanded with Typ_aux (Typ_id id, _) when id_string id = "nat" -> Some "Uint" | _ -> None
        )
    )

let constructor_for_function ctx env _ result_type = representation_class ctx env result_type

let construct_with constructor value =
  if String.equal constructor "int" && decimal_integer_literal value then value else constructor ^ "(" ^ value ^ ")"

let return_value ctx value =
  match ctx.current_return_constructor with None -> value | Some constructor -> construct_with constructor value

let construct_value ctx env typ value =
  match representation_class ctx env typ with None -> value | Some constructor -> construct_with constructor value

let construct_record_value ctx env typ value =
  match Env.expand_synonyms env typ with
  | Typ_aux (Typ_app (id, [A_aux (A_nexp _, _)]), _)
    when id_string id = "atom" || id_string id = "implicit" || id_string id = "itself" ->
      construct_with "int" value
  | _ -> construct_value ctx env typ value

let instantiate_record_field_type ~loc ctx record_id type_args typ =
  match Bindings.find_opt record_id ctx.record_quants with
  | None -> typ
  | Some typq ->
      let rec instantiate typ quantifiers args =
        match (quantifiers, args) with
        | [], [] -> typ
        | quantifier :: quantifiers, arg :: args ->
            instantiate (typ_subst (kopt_kid quantifier) arg typ) quantifiers args
        | _ -> backend_error ~loc ("record type arguments do not match quantifiers for " ^ id_string record_id)
      in
      instantiate typ (quant_kopts typq) type_args

let record_field_types ~loc ctx record_id type_args field_id =
  match Bindings.find_opt record_id ctx.record_fields with
  | None -> None
  | Some fields ->
      Option.map
        (fun (_, typ) -> (typ, instantiate_record_field_type ~loc ctx record_id type_args typ))
        (List.find_opt (fun (candidate, _) -> Id.compare candidate field_id = 0) fields)

let construct_record_field_value ctx env declared_typ instantiated_typ value =
  match representation_class ctx env instantiated_typ with
  | Some _ -> construct_with (python_typ ctx declared_typ) value
  | None -> construct_record_value ctx env instantiated_typ value

let python_bit = function Bit.B0 -> "0" | Bit.B1 -> "1"

let bit_literal bits =
  let digits = String.concat "" (List.map python_bit bits) in
  Printf.sprintf "Bits(%d, 0b%s)" (List.length bits) (if String.equal digits "" then "0" else digits)

let python_lit (L_aux (lit_aux, _)) =
  match lit_aux with
  | L_unit -> "None"
  | L_true -> "True"
  | L_false -> "False"
  | L_num number -> Big_int.to_string number
  | L_string value -> py_string value
  | L_real value -> "float(" ^ py_string (Q.to_string (Util.Rational.from_rocq value)) ^ ")"
  | L_bin bin -> bit_literal (BitList.of_bin_lit bin)
  | L_hex hex -> bit_literal (BitList.of_hex_lit hex)

let rec record_application ctx l exp =
  match Env.expand_synonyms (env_of exp) (typ_of exp) with
  | Typ_aux (Typ_id id, _) when IdSet.mem id ctx.records -> (id, [])
  | Typ_aux (Typ_app (id, args), _) when IdSet.mem id ctx.records -> (id, args)
  | typ -> backend_error ~loc:l ("record expression has non-record type " ^ string_of_typ typ)

let record_id ctx l exp = fst (record_application ctx l exp)

let record_validity_arguments ~loc ctx id args =
  match Bindings.find_opt id ctx.record_quants with
  | None -> []
  | Some typq ->
      let rec collect quantifiers args =
        match (quantifiers, args) with
        | [], [] -> []
        | KOpt_aux (KOpt_kind (K_aux (K_int, _), kid), _) :: quantifiers, A_aux (A_nexp value, _) :: args ->
            (kid_name kid ^ "=" ^ required_runtime_nexp ~loc ctx "record validity argument" value)
            :: collect quantifiers args
        | KOpt_aux (KOpt_kind (K_aux (K_bool, _), kid), _) :: quantifiers, A_aux (A_bool value, _) :: args ->
            let value = required_runtime_constraint ~loc ctx ctx.env "record validity argument" value in
            (kid_name kid ^ "=" ^ value) :: collect quantifiers args
        | KOpt_aux (KOpt_kind (K_aux (K_type, _), _), _) :: quantifiers, A_aux (A_typ _, _) :: args ->
            collect quantifiers args
        | _ -> backend_error ~loc ("record type arguments do not match quantifiers for " ^ id_string id)
      in
      collect (quant_kopts typq) args

let is_unit_typ env typ =
  match Env.expand_synonyms env typ with Typ_aux (Typ_id id, _) -> id_string id = "unit" | _ -> false

let function_type ctx id =
  match Bindings.find_opt id ctx.val_specs with
  | Some (Typ_aux (Typ_fn (args, result), _)) -> Some (args, result)
  | _ -> None

let rec recoverable_numeric_kids ctx env typ =
  let typ = try Env.expand_synonyms env typ with Type_internal.Type_error _ -> typ in
  match typ with
  | Typ_aux
      ( Typ_app
          (id, [A_aux (A_nexp (Nexp_aux (Nexp_var lower, _)), _); A_aux (A_nexp (Nexp_aux (Nexp_var upper, _)), _)]),
        _
      )
    when id_string id = "range" && Kid.compare lower upper = 0 ->
      KidSet.singleton lower
  | Typ_aux (Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _)]), _)
    when id_string id = "atom"
         || id_string id = "implicit"
         || id_string id = "itself"
         || id_string id = "bitvector"
         || id_string id = "bits" ->
      KidSet.singleton kid
  | Typ_aux (Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _); A_aux (A_typ _, _)]), _)
    when id_string id = "vector" ->
      KidSet.singleton kid
  | Typ_aux (Typ_app (id, args), _) when IdSet.mem id ctx.records && ctx.pydantic -> (
      match Bindings.find_opt id ctx.record_quants with
      | Some typq when record_has_validity ctx typq ->
          let rec collect recovered quantifiers args =
            match (quantifiers, args) with
            | [], [] -> recovered
            | ( KOpt_aux (KOpt_kind (K_aux (K_int, _), _), _) :: quantifiers,
                A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _) :: args )
            | ( KOpt_aux (KOpt_kind (K_aux (K_bool, _), _), _) :: quantifiers,
                A_aux (A_bool (NC_aux (NC_var kid, _)), _) :: args ) ->
                collect (KidSet.add kid recovered) quantifiers args
            | _ :: quantifiers, _ :: args -> collect recovered quantifiers args
            | _ -> recovered
          in
          collect KidSet.empty (quant_kopts typq) args
      | _ -> KidSet.empty
    )
  | Typ_aux (Typ_tuple typs, _) ->
      List.fold_left
        (fun recovered typ -> KidSet.union recovered (recoverable_numeric_kids ctx env typ))
        KidSet.empty typs
  | Typ_aux (Typ_exist (_, _, body), _) -> recoverable_numeric_kids ctx env body
  | _ -> KidSet.empty

let function_hidden_quantifiers ctx env id =
  if not ctx.pydantic then []
  else (
    match (Bindings.find_opt id ctx.function_quants, function_type ctx id) with
    | Some typq, Some (args, _) ->
        let recovered =
          List.fold_left
            (fun recovered typ -> KidSet.union recovered (recoverable_numeric_kids ctx env typ))
            KidSet.empty args
        in
        List.filter (fun (kid, _, _) -> not (KidSet.mem kid recovered)) (runtime_quantifiers typq)
    | _ -> []
  )

let call_args ctx env id args =
  match (function_type ctx id, args) with
  | Some ([typ], _), [E_aux (E_lit (L_aux (L_unit, _)), _)] when is_unit_typ env typ -> []
  | _ -> args

let function_hidden_arguments ctx (E_aux (_, (loc, tannot)) as exp) id =
  if not (IdSet.mem id ctx.functions) then []
  else (
    let env = env_of exp in
    let hidden = function_hidden_quantifiers ctx env id in
    if hidden = [] then []
    else (
      let instantiations =
        match get_instantiations tannot with
        | Some instantiations -> instantiations
        | None -> (
            try instantiation_of exp
            with Type_internal.Type_error _ ->
              backend_error ~loc ("cannot recover type instantiations for call to " ^ id_string id)
          )
      in
      List.map
        (fun (kid, _, _) ->
          match KBindings.find_opt kid instantiations with
          | Some arg -> (
              match runtime_typ_arg ctx arg with
              | Some value -> value
              | None ->
                  backend_error ~loc
                    ("cannot recover runtime value for implicit function argument " ^ string_of_kid kid ^ " in call to "
                   ^ id_string id
                    )
            )
          | None ->
              backend_error ~loc
                ("missing type instantiation for implicit function argument " ^ string_of_kid kid ^ " in call to "
               ^ id_string id
                )
        )
        hidden
    )
  )

let direct_builtin ~loc name args =
  let unary description render =
    match args with
    | [value] -> Some (render value)
    | _ -> backend_error ~loc (description ^ " expected exactly one runtime argument")
  in
  let binary description render =
    match args with
    | [left; right] -> Some (render left right)
    | _ -> backend_error ~loc (description ^ " expected exactly two runtime arguments")
  in
  let ternary description render =
    match args with
    | [first; second; third] -> Some (render first second third)
    | _ -> backend_error ~loc (description ^ " expected exactly three runtime arguments")
  in
  let integer value =
    if
      decimal_integer_literal value
      || (String.starts_with ~prefix:"int(" value && String.ends_with ~suffix:")" value)
      || (String.starts_with ~prefix:"len(" value && String.ends_with ~suffix:")" value)
    then value
    else "int(" ^ value ^ ")"
  in
  let integer_conversion = integer in
  let integer_binary description operator =
    binary description (fun left right -> "(" ^ integer left ^ " " ^ operator ^ " " ^ integer right ^ ")")
  in
  let value_binary description operator =
    binary description (fun left right -> "((" ^ left ^ ") " ^ operator ^ " (" ^ right ^ "))")
  in
  match name with
  | "add_int" -> integer_binary "integer addition" "+"
  | "sub_int" -> integer_binary "integer subtraction" "-"
  | "mult_int" -> integer_binary "integer multiplication" "*"
  | "negate" | "neg_int" -> unary "integer negation" (fun value -> "(-" ^ integer value ^ ")")
  | "abs_int" -> unary "integer absolute value" (fun value -> "abs(" ^ integer value ^ ")")
  | "max_int" -> binary "integer maximum" (fun left right -> "max(" ^ integer left ^ ", " ^ integer right ^ ")")
  | "min_int" -> binary "integer minimum" (fun left right -> "min(" ^ integer left ^ ", " ^ integer right ^ ")")
  | "lt" -> integer_binary "integer less-than" "<"
  | "lteq" -> integer_binary "integer less-than-or-equal" "<="
  | "gt" -> integer_binary "integer greater-than" ">"
  | "gteq" -> integer_binary "integer greater-than-or-equal" ">="
  | "eq_int" -> value_binary "integer equality" "=="
  | "neq_int" -> value_binary "integer inequality" "!="
  | "eq_bool" | "eq_bits" | "eq_anything" -> value_binary "equality" "=="
  | "neq_anything" -> value_binary "inequality" "!="
  | "eq_unit" -> binary "unit equality" (fun _ _ -> "True")
  | "pow2" -> unary "power of two" (fun exponent -> "(1 << " ^ integer exponent ^ ")")
  | "shl_int" -> integer_binary "integer left shift" "<<"
  | "shr_int" -> integer_binary "integer right shift" ">>"
  | "not" | "not_bool" -> unary "boolean negation" (fun value -> "(not (" ^ value ^ "))")
  | "and_bool" -> value_binary "boolean conjunction" "&"
  | "or_bool" -> value_binary "boolean disjunction" "|"
  | "length" | "vector_length" -> unary "sequence length" (fun value -> "len(" ^ value ^ ")")
  | "list_is_empty" -> unary "empty-list test" (fun value -> "(len(" ^ value ^ ") == 0)")
  | "string_append" | "concat_str" -> value_binary "string concatenation" "+"
  | "zeros" -> unary "zero bitvector" (fun width -> "Bits(" ^ integer width ^ ", 0)")
  | "ones" -> unary "one bitvector" (fun width -> "Bits(" ^ integer width ^ ", -1)")
  | "unsigned" | "unsigned_bits" | "sail_unsigned" ->
      unary "unsigned bitvector conversion" (fun value -> integer_conversion value)
  | "get_slice_int" ->
      ternary "integer bit slice" (fun width value start ->
          "Bits(" ^ integer width ^ ", " ^ integer value ^ " >> " ^ integer start ^ ")"
      )
  | "signed" | "signed_bits" | "sail_signed" ->
      unary "signed bitvector conversion" (fun value -> "(" ^ value ^ ").signed()")
  | "shiftl" | "shift_bits_left" ->
      binary "bitvector left shift" (fun value amount -> "((" ^ value ^ ") << " ^ integer amount ^ ")")
  | "shiftr" | "shift_bits_right" ->
      binary "bitvector right shift" (fun value amount -> "((" ^ value ^ ") >> " ^ integer amount ^ ")")
  | "arith_shiftr" | "arith_shift_bits_right" ->
      binary "arithmetic bitvector right shift" (fun value amount ->
          "(" ^ value ^ ").arith_shift_right(" ^ integer amount ^ ")"
      )
  | "not_bits" -> unary "bitvector complement" (fun value -> "(~(" ^ value ^ "))")
  | "xor_bits" -> value_binary "bitvector xor" "^"
  | "or_bits" -> value_binary "bitvector or" "|"
  | "and_bits" -> value_binary "bitvector and" "&"
  | "add_bits" | "add_bits_int" -> value_binary "bitvector addition" "+"
  | "sub_bits" -> value_binary "bitvector subtraction" "-"
  | "mult_bits" -> value_binary "bitvector multiplication" "*"
  | "count_leading_zeros" -> unary "leading-zero count" (fun value -> "(" ^ value ^ ").count_leading_zeros()")
  | "count_trailing_zeros" -> unary "trailing-zero count" (fun value -> "(" ^ value ^ ").count_trailing_zeros()")
  | "sail_truncateLSB" | "truncateLSB" | "truncate_lsb" ->
      binary "least-significant-bit truncation" (fun value width ->
          "(" ^ value ^ ").truncate_lsb(" ^ integer width ^ ")"
      )
  | "string_of_bits" -> unary "bitvector formatting" (fun value -> "(" ^ value ^ ").to_bin()")
  | "eq_string" -> value_binary "string equality" "=="
  | _ -> None

let known_builtin = function
  | "ediv_int" -> Some "sail_ediv_int"
  | "emod_int" -> Some "sail_emod_int"
  | "tdiv_int" -> Some "sail_tdiv_int"
  | "tmod_int" -> Some "sail_tmod_int"
  | "quotient" -> Some "sail_ediv_int"
  | "remainder" -> Some "sail_emod_int"
  | "pow_int" -> Some "sail_pow_int"
  | "sail_cons" | "cons" -> Some "sail_cons"
  | "vector_init" -> Some "sail_vector_init"
  | "internal_pick" | "pick" -> Some "sail_pick"
  | "append" | "vector_append" -> Some "sail_vector_append"
  | "append_64" -> Some "sail_append_64"
  | "decimal_string_of_int" | "dec_str" -> Some "sail_decimal_string_of_int"
  | "hex_str" -> Some "sail_hex_string_of_int"
  | "print" -> Some "sail_print"
  | "print_endline" -> Some "sail_print_endline"
  | "prerr" -> Some "sail_prerr"
  | "prerr_endline" -> Some "sail_prerr_endline"
  | "print_int" -> Some "sail_print_int"
  | "prerr_int" -> Some "sail_prerr_int"
  | "size_itself_int" | "make_the_value" -> Some "int"
  | _ -> None

type pattern = { pattern : string; guards : string list; irrefutable : bool }

let combine_pattern code patterns =
  {
    pattern = code (List.map (fun item -> item.pattern) patterns);
    guards = concat_map (fun item -> item.guards) patterns;
    irrefutable = List.for_all (fun item -> item.irrefutable) patterns;
  }

let rec python_pat ctx (P_aux (pat_aux, (l, _)) as pat) =
  match pat_aux with
  | P_id id -> (
      match Env.lookup_id id (env_of_pat pat) with
      | Enum _ -> { pattern = value_name ctx id; guards = []; irrefutable = false }
      | Register _ -> backend_error ~loc:l ("cannot bind register " ^ id_string id ^ " in a Python pattern")
      | Local _ | Unbound _ -> { pattern = safe_local_name id; guards = []; irrefutable = true }
    )
  | P_lit (L_aux (((L_bin _ | L_hex _) as lit_aux), lit_l)) ->
      let binding = fresh ctx "bits_pattern" in
      let literal = python_lit (L_aux (lit_aux, lit_l)) in
      { pattern = binding; guards = [binding ^ " == " ^ literal]; irrefutable = false }
  | P_lit lit -> { pattern = python_lit lit; guards = []; irrefutable = false }
  | P_typ (_, pat) | P_var (pat, _) -> python_pat ctx pat
  | P_tuple pats ->
      let pats = List.map (python_pat ctx) pats in
      combine_pattern
        (fun items -> "(" ^ String.concat ", " items ^ (if List.length items = 1 then "," else "") ^ ")")
        pats
  | P_vector pats | P_list pats ->
      let pats = List.map (python_pat ctx) pats in
      combine_pattern (fun items -> "[" ^ String.concat ", " items ^ "]") pats
  | P_wild -> { pattern = "_"; guards = []; irrefutable = true }
  | P_as (pat, id) ->
      let pat = python_pat ctx pat in
      { pat with pattern = "(" ^ pat.pattern ^ " as " ^ safe_local_name id ^ ")" }
  | P_app (id, pats) -> (
      match (native_option_constructor (env_of_pat pat) id, pats) with
      | Some `None, _ -> { pattern = "None"; guards = []; irrefutable = false }
      | Some `Some, [payload] ->
          let payload = python_pat ctx payload in
          let binding = fresh ctx "some_value" in
          {
            pattern = "(" ^ payload.pattern ^ " as " ^ binding ^ ")";
            guards = payload.guards @ [binding ^ " is not None"];
            irrefutable = false;
          }
      | Some `Some, _ -> backend_error ~loc:l "Sail Some pattern expected exactly one payload"
      | None, _ ->
          let pats = List.map (python_pat ctx) pats in
          let result =
            combine_pattern (fun items -> constructor_name ctx id ^ "(" ^ String.concat ", " items ^ ")") pats
          in
          { result with irrefutable = false }
    )
  | P_cons (head, tail) ->
      let head = python_pat ctx head in
      let tail = python_pat ctx tail in
      let tail_pattern =
        match tail.pattern with
        | "_" -> "*_"
        | value when tail.irrefutable -> "*" ^ value
        | _ -> backend_error ~loc:l "list-tail patterns must bind a name after Python rewrites"
      in
      {
        pattern = "[" ^ head.pattern ^ ", " ^ tail_pattern ^ "]";
        guards = head.guards @ tail.guards;
        irrefutable = false;
      }
  | P_struct (_, fields, _) ->
      let fields =
        List.map
          (fun (id, pat) ->
            let pat = python_pat ctx pat in
            (py_id id ^ "=" ^ pat.pattern, pat)
          )
          fields
      in
      let record =
        match Env.expand_synonyms (env_of_pat pat) (typ_of_pat pat) with
        | Typ_aux (Typ_id id, _) | Typ_aux (Typ_app (id, _), _) -> type_name ctx id
        | typ -> backend_error ~loc:l ("struct pattern has non-record type " ^ string_of_typ typ)
      in
      {
        pattern = record ^ "(" ^ String.concat ", " (List.map fst fields) ^ ")";
        guards = concat_map (fun (_, pat) -> pat.guards) fields;
        irrefutable = false;
      }
  | P_or (left, right) ->
      let left = python_pat ctx left in
      let right = python_pat ctx right in
      if left.guards <> [] || right.guards <> [] then
        backend_error ~loc:l "guarded alternatives are not supported in Python patterns";
      { pattern = "(" ^ left.pattern ^ " | " ^ right.pattern ^ ")"; guards = []; irrefutable = false }
  | P_not _ -> backend_error ~loc:l "negative pattern survived the Python rewrite pipeline"
  | P_vector_concat _ -> backend_error ~loc:l "vector-concatenation pattern survived the Python rewrite pipeline"
  | P_vector_subrange _ -> backend_error ~loc:l "vector-subrange pattern survived the Python rewrite pipeline"
  | P_string_append _ -> backend_error ~loc:l "string-append pattern survived the Python rewrite pipeline"

let guard_clause guards = match guards with [] -> "" | _ -> " if " ^ String.concat " and " guards

let rec assignment_pattern ctx (P_aux (pat_aux, _) as pat) =
  match pat_aux with
  | P_id id -> (
      match Env.lookup_id id (env_of_pat pat) with Local _ | Unbound _ -> Some (safe_local_name id) | _ -> None
    )
  | P_wild -> Some "_"
  | P_typ (_, pat) | P_var (pat, _) -> assignment_pattern ctx pat
  | P_tuple pats ->
      let pats = List.map (assignment_pattern ctx) pats in
      if List.for_all Option.is_some pats then
        Some ("(" ^ String.concat ", " (List.map Option.get pats) ^ (if List.length pats = 1 then "," else "") ^ ")")
      else None
  | P_list pats ->
      let pats = List.map (assignment_pattern ctx) pats in
      if List.for_all Option.is_some pats then Some ("[" ^ String.concat ", " (List.map Option.get pats) ^ "]")
      else None
  | _ -> None

let add_pattern_numeric_values ctx values pat =
  let rec collect values (P_aux (pat_aux, _)) =
    match pat_aux with
    | P_var (inner, TP_aux (TP_var kid, _)) ->
        let values =
          match assignment_pattern ctx inner with
          | Some target when not (String.equal target "_") -> KBindings.add kid (runtime_numeric_value target) values
          | _ -> values
        in
        collect values inner
    | P_var (inner, _) -> collect values inner
    | P_typ (_, inner) | P_as (inner, _) -> collect values inner
    | P_tuple pats | P_vector pats | P_list pats -> List.fold_left collect values pats
    | P_cons (head, tail) | P_or (head, tail) -> collect (collect values head) tail
    | P_app (_, pats) -> List.fold_left collect values pats
    | P_struct (_, fields, _) -> List.fold_left (fun values (_, pat) -> collect values pat) values fields
    | _ -> values
  in
  collect values pat

let pattern_numeric_values ctx pat = add_pattern_numeric_values ctx ctx.numeric_values pat

let with_pattern_numeric_values ctx pat render = with_numeric_values ctx (pattern_numeric_values ctx pat) render

let with_patterns_numeric_values ctx pats render =
  with_numeric_values ctx (List.fold_left (add_pattern_numeric_values ctx) ctx.numeric_values pats) render

let rec lexp_bound_ids (LE_aux (lexp_aux, _)) =
  match lexp_aux with
  | LE_id id | LE_typ (_, id) -> [id]
  | LE_tuple items -> concat_map lexp_bound_ids items
  | LE_field _ | LE_vector _ | LE_deref _ | LE_vector_range _ | LE_vector_concat _ -> []

let rec lexp ctx (LE_aux (lexp_aux, ((l, _) as annot))) =
  match lexp_aux with
  | LE_id id | LE_typ (_, id) -> (
      match Env.lookup_id id (env_of_annot annot) with
      | Local _ | Unbound _ -> safe_local_name id
      | Register _ | Enum _ -> source_value_name ctx id
    )
  | LE_tuple items -> "(" ^ String.concat ", " (List.map (lexp ctx) items) ^ ")"
  | LE_field (base, field) -> lexp ctx base ^ "." ^ py_id field
  | LE_vector (base, index) ->
      let before, index = lower_value ctx index in
      if before <> [] then backend_error ~loc:l "effectful vector index survived expression lifting";
      lexp ctx base ^ "[" ^ index ^ "]"
  | LE_deref value ->
      let before, value = lower_value ctx value in
      if before <> [] then backend_error ~loc:l "effectful reference target survived expression lifting";
      value ^ ".value"
  | LE_vector_range _ -> backend_error ~loc:l "vector-range assignment survived the Python rewrite pipeline"
  | LE_vector_concat _ -> backend_error ~loc:l "vector-concatenation assignment survived the Python rewrite pipeline"

and lower_values ctx values =
  List.fold_left
    (fun (lines, expressions) value ->
      let before, expression = lower_value ctx value in
      (lines @ before, expressions @ [expression])
    )
    ([], []) values

and generated_enum_conversion_call ctx ~loc id args =
  let unary_arg description =
    match args with [arg] -> arg | _ -> backend_error ~loc (description ^ " expected exactly one runtime argument")
  in
  match Bindings.find_opt id ctx.to_enum_functions with
  | Some enum_id ->
      let arg = unary_arg "generated enum conversion" in
      Some (type_name ctx enum_id ^ "(" ^ arg ^ ")")
  | None -> (
      match Bindings.find_opt id ctx.from_enum_functions with
      | Some _ ->
          let arg = unary_arg "generated enum conversion" in
          Some ("(" ^ arg ^ ").value")
      | None -> None
    )

and lower_app ctx (E_aux (_, (l, _)) as exp) id args =
  let env = env_of exp in
  let args = call_args ctx env id args in
  let before, args = lower_values ctx args in
  match native_option_constructor env id with
  | Some `None -> (before, "None")
  | Some `Some -> (
      match args with
      | [payload] -> (before, payload)
      | _ -> backend_error ~loc:l "Sail Some constructor expected exactly one payload"
    )
  | None -> (
      match Env.union_constructor_info id env with
      | Some _ -> (before, constructor_name ctx id ^ "(" ^ String.concat ", " args ^ ")")
      | None -> (
          match generated_enum_conversion_call ctx ~loc:l id args with
          | Some call -> (before, call)
          | None ->
              let sail_name = id_string id in
              let external_name = Bindings.find_opt id ctx.externs in
              let operation = Option.value external_name ~default:sail_name in
              let operation = String.split_on_char '<' operation |> List.hd in
              let function_call name args = name ^ "(" ^ String.concat ", " args ^ ")" in
              let call =
                if IdSet.mem id ctx.undefined_functions then ("sail_undefined(" ^ py_string sail_name ^ ")", false)
                else (
                  match operation with
                  | "vector_access" | "vector_access_dec" | "bitvector_access" ->
                      (function_call "sail_vector_access" (args @ ["False"]), false)
                  | "vector_access_inc" | "bitvector_access_inc" ->
                      (function_call "sail_vector_access" (args @ ["True"]), false)
                  | "vector_update" | "vector_update_dec" ->
                      (function_call "sail_vector_update" (args @ ["False"]), false)
                  | "vector_update_inc" -> (function_call "sail_vector_update" (args @ ["True"]), false)
                  | "vector_subrange" -> (function_call "sail_vector_subrange" (args @ ["False"]), false)
                  | "vector_subrange_inc" -> (function_call "sail_vector_subrange" (args @ ["True"]), false)
                  | "vector_update_subrange" -> (function_call "sail_vector_update_subrange" (args @ ["False"]), false)
                  | "vector_update_subrange_inc" ->
                      (function_call "sail_vector_update_subrange" (args @ ["True"]), false)
                  | "zero_extend" | "zero_extend_bits" ->
                      let call =
                        if List.length args = 1 then (
                          let width =
                            match Env.expand_synonyms env (typ_of exp) with
                            | Typ_aux (Typ_app (id, [A_aux (A_nexp width, _)]), _) when id_string id = "bitvector" ->
                                required_runtime_nexp ~loc:l ctx "zero-extension width" width
                            | _ -> backend_error ~loc:l "cannot infer target width for zero extension"
                          in
                          "(" ^ List.hd args ^ ").zero_extend(" ^ width ^ ")"
                        )
                        else (
                          match args with
                          | [value; width] -> "(" ^ value ^ ").zero_extend(" ^ width ^ ")"
                          | _ -> backend_error ~loc:l "zero extension expected one or two runtime arguments"
                        )
                      in
                      (call, false)
                  | "sign_extend" | "sign_extend_bits" ->
                      let call =
                        if List.length args = 1 then (
                          let width =
                            match Env.expand_synonyms env (typ_of exp) with
                            | Typ_aux (Typ_app (id, [A_aux (A_nexp width, _)]), _) when id_string id = "bitvector" ->
                                required_runtime_nexp ~loc:l ctx "sign-extension width" width
                            | _ -> backend_error ~loc:l "cannot infer target width for sign extension"
                          in
                          "(" ^ List.hd args ^ ").sign_extend(" ^ width ^ ")"
                        )
                        else (
                          match args with
                          | [value; width] -> "(" ^ value ^ ").sign_extend(" ^ width ^ ")"
                          | _ -> backend_error ~loc:l "sign extension expected one or two runtime arguments"
                        )
                      in
                      (call, false)
                  | "sail_truncate" | "truncate" ->
                      let call =
                        if List.length args = 1 then (
                          let width =
                            match Env.expand_synonyms env (typ_of exp) with
                            | Typ_aux (Typ_app (id, [A_aux (A_nexp width, _)]), _) when id_string id = "bitvector" ->
                                required_runtime_nexp ~loc:l ctx "bitvector-truncation width" width
                            | _ -> backend_error ~loc:l "cannot infer target width for bitvector truncation"
                          in
                          "Bits(" ^ width ^ ", int(" ^ List.hd args ^ "))"
                        )
                        else (
                          match args with
                          | [value; width] -> "Bits(" ^ width ^ ", int(" ^ value ^ "))"
                          | _ -> backend_error ~loc:l "bitvector truncation expected one or two runtime arguments"
                        )
                      in
                      (call, false)
                  | name -> (
                      match direct_builtin ~loc:l name args with
                      | Some expression -> (expression, false)
                      | None -> (
                          match known_builtin name with
                          | Some runtime -> (function_call runtime args, false)
                          | None -> (
                              match external_name with
                              | Some external_target ->
                                  let target =
                                    match ctx.extern_module with
                                    | Some _ -> extern_binding_name external_target
                                    | None -> "call_extern"
                                  in
                                  let arguments =
                                    match ctx.extern_module with
                                    | Some _ -> args
                                    | None -> py_string external_target :: args
                                  in
                                  (function_call target arguments, true)
                              | None ->
                                  let args = args @ function_hidden_arguments ctx exp id in
                                  (function_call (source_value_name ctx id) args, false)
                            )
                        )
                    )
                )
              in
              let call = fst call in
              (before, call)
        )
    )

and lower_value ctx (E_aux (exp_aux, (l, _)) as exp) =
  match exp_aux with
  | E_id id -> ([], if IdSet.mem id ctx.local_ids then safe_local_name id else source_value_name ctx id)
  | E_lit lit -> ([], python_lit lit)
  | E_typ (_, exp) | E_internal_assume (_, exp) -> lower_value ctx exp
  | E_app (id, args) -> lower_app ctx exp id args
  | E_tuple values ->
      let before, values = lower_values ctx values in
      (before, "(" ^ String.concat ", " values ^ (if List.length values = 1 then "," else "") ^ ")")
  | E_vector values ->
      let before, values = lower_values ctx values in
      let value = "[" ^ String.concat ", " values ^ "]" in
      let value =
        match Env.expand_synonyms (env_of exp) (typ_of exp) with
        | Typ_aux (Typ_app (id, [A_aux (A_nexp width, _)]), _) when id_string id = "bitvector" ->
            let width = Option.value (runtime_nexp ctx width) ~default:(string_of_int (List.length values)) in
            "sail_bitvector(" ^ value ^ ", " ^ width ^ ")"
        | _ -> value
      in
      (before, value)
  | E_list values ->
      let before, values = lower_values ctx values in
      (before, "[" ^ String.concat ", " values ^ "]")
  | E_cons (head, tail) ->
      let before_head, head = lower_value ctx head in
      let before_tail, tail = lower_value ctx tail in
      (before_head @ before_tail, "[" ^ head ^ ", *" ^ tail ^ "]")
  | E_vector_append (left, right) ->
      let before_left, left = lower_value ctx left in
      let before_right, right = lower_value ctx right in
      (before_left @ before_right, "sail_vector_append(" ^ left ^ ", " ^ right ^ ")")
  | E_struct (_, fields) ->
      let record_id, type_args = record_application ctx l exp in
      let record = type_name ctx record_id in
      let lines, fields =
        List.fold_left
          (fun (lines, fields) (FE_aux (FE_fexp (id, value), _)) ->
            let before, value = lower_value ctx value in
            let value =
              match record_field_types ~loc:l ctx record_id type_args id with
              | Some (declared_typ, instantiated_typ) ->
                  construct_record_field_value ctx (env_of exp) declared_typ instantiated_typ value
              | None -> value
            in
            (lines @ before, fields @ [py_id id ^ "=" ^ value])
          )
          ([], []) fields
      in
      let fields =
        match Bindings.find_opt record_id ctx.record_quants with
        | Some typq when record_has_validity ctx typq ->
            let validity = validity_type_name ctx record_id in
            let arguments = record_validity_arguments ~loc:l ctx record_id type_args in
            ("validity=" ^ validity ^ "(" ^ String.concat ", " arguments ^ ")") :: fields
        | _ -> fields
      in
      (lines, record ^ "(" ^ String.concat ", " fields ^ ")")
  | E_struct_update (base_exp, fields) ->
      let owner, type_args = record_application ctx l base_exp in
      let before, base = lower_value ctx base_exp in
      let lines, fields =
        List.fold_left
          (fun (lines, fields) (FE_aux (FE_fexp (id, value), _)) ->
            let value_lines, value = lower_value ctx value in
            let value =
              match record_field_types ~loc:l ctx owner type_args id with
              | Some (declared_typ, instantiated_typ) ->
                  construct_record_field_value ctx (env_of exp) declared_typ instantiated_typ value
              | None -> value
            in
            (lines @ value_lines, fields @ [py_id id ^ "=" ^ value])
          )
          (before, []) fields
      in
      (lines, "replace(deepcopy(" ^ base ^ "), " ^ String.concat ", " fields ^ ")")
  | E_field (base, field) ->
      let before, base = lower_value ctx base in
      (before, base ^ "." ^ py_id field)
  | E_sizeof size -> ([], required_runtime_nexp ~loc:l ctx "sizeof expression" size)
  | E_ref id ->
      let namespace =
        match (ctx.qualify_globals, ctx.current_module, Bindings.find_opt id ctx.register_modules) with
        | true, Some current_module, Some target_module when not (same_module current_module target_module) ->
            ctx.referenced_modules <- StringSet.add (module_key target_module) ctx.referenced_modules;
            imported_module_name ctx current_module target_module ^ ".__dict__"
        | _ -> "globals()"
      in
      ([], "SailRef(" ^ py_string (safe_value_name id) ^ ", " ^ namespace ^ ")")
  | E_config path -> ([], "sail_config(" ^ String.concat ", " (List.map py_string path) ^ ")")
  | E_constraint _ -> ([], "sail_constraint()")
  | E_undef -> ([], "sail_undefined(" ^ py_string (string_of_typ (typ_of exp)) ^ ")")
  | E_internal_value _ -> backend_error ~loc:l "interpreter-only value reached Python extraction"
  | E_block [] -> ([], "None")
  | E_block [value] -> lower_value ctx value
  | E_if (condition, yes, no) ->
      let before_condition, condition = lower_value ctx condition in
      let before_yes, yes = lower_value ctx yes in
      let before_no, no = lower_value ctx no in
      if before_yes = [] && before_no = [] then (before_condition, "(" ^ yes ^ " if " ^ condition ^ " else " ^ no ^ ")")
      else (
        let temporary = fresh ctx "value" in
        (emit_into ctx temporary exp, temporary)
      )
  | E_loop _ | E_for _ | E_match _ | E_let _ | E_assign _ | E_return _ | E_exit _ | E_throw _ | E_try _ | E_assert _
  | E_var _ | E_block _ | E_internal_plet _ | E_internal_return _ ->
      let temporary = fresh ctx "value" in
      (emit_into ctx temporary exp, temporary)

and emit_pattern_scope ctx value pat body =
  match assignment_pattern ctx pat with
  | Some "_" -> value :: body
  | Some target -> (target ^ " = " ^ value) :: body
  | None ->
      let pat = python_pat ctx pat in
      block
        ("match " ^ value ^ ":")
        (block ("case " ^ pat.pattern ^ guard_clause pat.guards ^ ":") body
        @ block "case _:" ["raise SailMatchFailure(" ^ py_string "Sail let-pattern did not match" ^ ")"]
        )

and emit_binding ctx pat binding body =
  match assignment_pattern ctx pat with
  | Some "_" -> emit_structural_stmt ctx binding @ body
  | Some target -> emit_into ctx target binding @ body
  | None ->
      let before, binding = lower_value ctx binding in
      before @ emit_pattern_scope ctx binding pat body

and emit_cases ctx target value clauses failure =
  let rec emit = function
    | [] -> ([], false)
    | Pat_aux (clause, _) :: clauses -> (
        match clause with
        | Pat_exp (pattern, body) ->
            let local_ids = bound_ids pattern in
            let source_pattern = pattern in
            let pattern = python_pat ctx source_pattern in
            let current =
              block
                ("case " ^ pattern.pattern ^ guard_clause pattern.guards ^ ":")
                (with_local_ids ctx local_ids (fun () ->
                     with_pattern_numeric_values ctx source_pattern (fun () -> emit_into ctx target body)
                 )
                )
            in
            if pattern.irrefutable && pattern.guards = [] then (current, true)
            else (
              let rest, exhaustive = emit clauses in
              (current @ rest, exhaustive)
            )
        | Pat_when (pattern, condition, body) ->
            let local_ids = bound_ids pattern in
            let source_pattern = pattern in
            let pattern = python_pat ctx source_pattern in
            let before, condition, body =
              with_local_ids ctx local_ids (fun () ->
                  with_pattern_numeric_values ctx source_pattern (fun () ->
                      let before, condition = lower_value ctx condition in
                      (before, condition, emit_into ctx target body)
                  )
              )
            in
            if before <> [] then backend_error "effectful match guard survived expression lifting";
            let guards = pattern.guards @ [condition] in
            let current = block ("case " ^ pattern.pattern ^ guard_clause guards ^ ":") body in
            let rest, exhaustive = emit clauses in
            (current @ rest, exhaustive)
      )
  in
  let cases, exhaustive = emit clauses in
  block ("match " ^ value ^ ":") (cases @ if exhaustive then [] else block "case _:" failure)

and emit_return_cases ctx result_type value clauses failure =
  let rec emit = function
    | [] -> ([], false)
    | Pat_aux (clause, _) :: clauses -> (
        match clause with
        | Pat_exp (pattern, body) ->
            let local_ids = bound_ids pattern in
            let source_pattern = pattern in
            let pattern = python_pat ctx source_pattern in
            let current =
              block
                ("case " ^ pattern.pattern ^ guard_clause pattern.guards ^ ":")
                (with_local_ids ctx local_ids (fun () ->
                     with_pattern_numeric_values ctx source_pattern (fun () -> emit_return ctx result_type body)
                 )
                )
            in
            if pattern.irrefutable && pattern.guards = [] then (current, true)
            else (
              let rest, exhaustive = emit clauses in
              (current @ rest, exhaustive)
            )
        | Pat_when (pattern, condition, body) ->
            let local_ids = bound_ids pattern in
            let source_pattern = pattern in
            let pattern = python_pat ctx source_pattern in
            let before, condition, body =
              with_local_ids ctx local_ids (fun () ->
                  with_pattern_numeric_values ctx source_pattern (fun () ->
                      let before, condition = lower_value ctx condition in
                      (before, condition, emit_return ctx result_type body)
                  )
              )
            in
            if before <> [] then backend_error "effectful match guard survived expression lifting";
            let guards = pattern.guards @ [condition] in
            let current = block ("case " ^ pattern.pattern ^ guard_clause guards ^ ":") body in
            let rest, exhaustive = emit clauses in
            (current @ rest, exhaustive)
      )
  in
  let cases, exhaustive = emit clauses in
  block ("match " ^ value ^ ":") (cases @ if exhaustive then [] else block "case _:" failure)

and emit_statement_cases ctx value clauses failure =
  let rec emit = function
    | [] -> ([], false)
    | Pat_aux (clause, _) :: clauses -> (
        match clause with
        | Pat_exp (pattern, body) ->
            let local_ids = bound_ids pattern in
            let source_pattern = pattern in
            let pattern = python_pat ctx source_pattern in
            let current =
              block
                ("case " ^ pattern.pattern ^ guard_clause pattern.guards ^ ":")
                (with_local_ids ctx local_ids (fun () ->
                     with_pattern_numeric_values ctx source_pattern (fun () -> emit_structural_stmt ctx body)
                 )
                )
            in
            if pattern.irrefutable && pattern.guards = [] then (current, true)
            else (
              let rest, exhaustive = emit clauses in
              (current @ rest, exhaustive)
            )
        | Pat_when (pattern, condition, body) ->
            let local_ids = bound_ids pattern in
            let source_pattern = pattern in
            let pattern = python_pat ctx source_pattern in
            let before, condition, body =
              with_local_ids ctx local_ids (fun () ->
                  with_pattern_numeric_values ctx source_pattern (fun () ->
                      let before, condition = lower_value ctx condition in
                      (before, condition, emit_structural_stmt ctx body)
                  )
              )
            in
            if before <> [] then backend_error "effectful match guard survived expression lifting";
            let guards = pattern.guards @ [condition] in
            let current = block ("case " ^ pattern.pattern ^ guard_clause guards ^ ":") body in
            let rest, exhaustive = emit clauses in
            (current @ rest, exhaustive)
      )
  in
  let cases, exhaustive = emit clauses in
  block ("match " ^ value ^ ":") (cases @ if exhaustive then [] else block "case _:" failure)

and emit_assignment ctx target_lexp value =
  let target = lexp ctx target_lexp in
  let target_typ = Type_check.typ_of_lexp target_lexp in
  let assign expression = target ^ " = " ^ construct_value ctx (env_of value) target_typ expression in
  match value with
  | E_aux
      ( ( E_block _ | E_let _ | E_internal_plet _ | E_var _ | E_if _ | E_match _ | E_try _ | E_assign _ | E_assert _
        | E_for _ | E_loop _ | E_return _ | E_internal_return _ | E_throw _ | E_exit _ ),
        _
      ) ->
      let temporary = fresh ctx "assigned_value" in
      emit_into ctx temporary value @ [assign temporary]
  | _ ->
      let before, value_expression = lower_value ctx value in
      before @ [target ^ " = " ^ construct_value ctx (env_of value) target_typ value_expression]

and emit_return ctx result_type (E_aux (exp_aux, annot) as exp) =
  let return value = "return " ^ return_value ctx value in
  match exp_aux with
  | E_block [] -> [return "None"]
  | E_block [last] -> emit_return ctx result_type last
  | E_block (head :: tail) -> emit_structural_stmt ctx head @ emit_return ctx result_type (E_aux (E_block tail, annot))
  | E_let (pat, binding, body) | E_internal_plet (pat, binding, body) ->
      let body =
        with_local_ids ctx (bound_ids pat) (fun () ->
            with_pattern_numeric_values ctx pat (fun () -> emit_return ctx result_type body)
        )
      in
      emit_binding ctx pat binding body
  | E_var (target_lexp, initial, body) ->
      let body = with_local_ids ctx (lexp_bound_ids target_lexp) (fun () -> emit_return ctx result_type body) in
      emit_into ctx (lexp ctx target_lexp) initial @ body
  | E_if (condition, yes, no) ->
      let before, condition = lower_value ctx condition in
      before
      @ block ("if " ^ condition ^ ":") (emit_return ctx result_type yes)
      @ block "else:" (emit_return ctx result_type no)
  | E_match (value, clauses) ->
      let before, value = lower_value ctx value in
      before
      @ emit_return_cases ctx result_type value clauses
          ["raise SailMatchFailure(" ^ py_string "no Sail match clause applied" ^ ")"]
  | E_try (body, clauses) ->
      let exception_name = fresh ctx "thrown" in
      block "try:" (emit_return ctx result_type body)
      @ block
          ("except SailThrown as " ^ exception_name ^ ":")
          (emit_return_cases ctx result_type (exception_name ^ ".value") clauses ["raise"])
  | E_assign (target, value) -> emit_assignment ctx target value @ [return "None"]
  | E_assert _ | E_for _ | E_loop _ -> emit_structural_stmt ctx exp @ [return "None"]
  | E_return _ | E_internal_return _ | E_throw _ | E_exit _ -> emit_stmt ctx exp
  | _ ->
      let before, value = lower_value ctx exp in
      before @ [return value]

and emit_structural_stmt ctx (E_aux (exp_aux, _) as exp) =
  match exp_aux with
  | E_block expressions -> concat_map (emit_structural_stmt ctx) expressions
  | E_let (pat, binding, body) | E_internal_plet (pat, binding, body) ->
      let body =
        with_local_ids ctx (bound_ids pat) (fun () ->
            with_pattern_numeric_values ctx pat (fun () -> emit_structural_stmt ctx body)
        )
      in
      emit_binding ctx pat binding body
  | E_var (target_lexp, initial, body) ->
      let body = with_local_ids ctx (lexp_bound_ids target_lexp) (fun () -> emit_structural_stmt ctx body) in
      emit_into ctx (lexp ctx target_lexp) initial @ body
  | E_for (id, start, finish, step, Ord_aux (order, _), body) ->
      let before_start, start = lower_value ctx start in
      let before_finish, finish = lower_value ctx finish in
      let before_step, step = lower_value ctx step in
      let increasing = match order with Ord_inc -> "True" | Ord_dec -> "False" in
      before_start @ before_finish @ before_step
      @ block
          ("for " ^ safe_local_name id ^ " in sail_range(" ^ start ^ ", " ^ finish ^ ", " ^ step ^ ", " ^ increasing
         ^ "):"
          )
          (with_local_ids ctx [id] (fun () -> emit_structural_stmt ctx body))
  | E_loop (While, _, condition, body) ->
      let before, condition = lower_value ctx condition in
      block "while True:" (before @ block ("if not (" ^ condition ^ "):") ["break"] @ emit_structural_stmt ctx body)
  | E_loop (Until, _, condition, body) ->
      let before, condition = lower_value ctx condition in
      block "while True:" (emit_structural_stmt ctx body @ before @ block ("if " ^ condition ^ ":") ["break"])
  | E_if (condition, yes, no) ->
      let before, condition = lower_value ctx condition in
      let no = emit_structural_stmt ctx no in
      before @ block ("if " ^ condition ^ ":") (emit_structural_stmt ctx yes) @ if no = [] then [] else block "else:" no
  | E_match (value, clauses) ->
      let before, value = lower_value ctx value in
      before
      @ emit_statement_cases ctx value clauses
          ["raise SailMatchFailure(" ^ py_string "no Sail match clause applied" ^ ")"]
  | E_try (body, clauses) ->
      let exception_name = fresh ctx "thrown" in
      block "try:" (emit_structural_stmt ctx body)
      @ block
          ("except SailThrown as " ^ exception_name ^ ":")
          (emit_statement_cases ctx (exception_name ^ ".value") clauses ["raise"])
  | E_assert (condition, message) ->
      let before_condition, condition = lower_value ctx condition in
      let before_message, message = lower_value ctx message in
      before_condition @ before_message @ block ("if not (" ^ condition ^ "):") ["raise SailError(" ^ message ^ ")"]
  | E_lit (L_aux (L_unit, _)) -> []
  | E_assign _ | E_return _ | E_internal_return _ | E_throw _ | E_exit _ -> emit_stmt ctx exp
  | _ ->
      let before, value = lower_value ctx exp in
      before @ [value]

and emit_into ctx target (E_aux (exp_aux, annot) as exp) =
  match exp_aux with
  | E_block [] -> [target ^ " = None"]
  | E_block [last] -> emit_into ctx target last
  | E_block (head :: tail) -> emit_stmt ctx head @ emit_into ctx target (E_aux (E_block tail, annot))
  | E_let (pat, binding, body) | E_internal_plet (pat, binding, body) ->
      let body =
        with_local_ids ctx (bound_ids pat) (fun () ->
            with_pattern_numeric_values ctx pat (fun () -> emit_into ctx target body)
        )
      in
      emit_binding ctx pat binding body
  | E_var (target_lexp, initial, body) ->
      let body = with_local_ids ctx (lexp_bound_ids target_lexp) (fun () -> emit_into ctx target body) in
      emit_into ctx (lexp ctx target_lexp) initial @ body
  | E_if (condition, yes, no) ->
      let before, condition = lower_value ctx condition in
      before @ block ("if " ^ condition ^ ":") (emit_into ctx target yes) @ block "else:" (emit_into ctx target no)
  | E_match (value, clauses) ->
      let before, value = lower_value ctx value in
      before
      @ emit_cases ctx target value clauses ["raise SailMatchFailure(" ^ py_string "no Sail match clause applied" ^ ")"]
  | E_try (body, clauses) ->
      let exception_name = fresh ctx "thrown" in
      block "try:" (emit_into ctx target body)
      @ block
          ("except SailThrown as " ^ exception_name ^ ":")
          (emit_cases ctx target (exception_name ^ ".value") clauses ["raise"])
  | E_assign (target_lexp, value) -> emit_assignment ctx target_lexp value @ [target ^ " = None"]
  | E_return value | E_internal_return value ->
      let before, value = lower_value ctx value in
      before @ ["raise SailReturn(" ^ value ^ ")"]
  | E_throw value ->
      let before, value = lower_value ctx value in
      before @ ["raise SailThrown(" ^ value ^ ")"]
  | E_exit value ->
      let before, value = lower_value ctx value in
      before @ ["raise SailExit(" ^ value ^ ")"]
  | E_assert (condition, message) ->
      let before_condition, condition = lower_value ctx condition in
      let before_message, message = lower_value ctx message in
      before_condition @ before_message
      @ block ("if not (" ^ condition ^ "):") ["raise SailError(" ^ message ^ ")"]
      @ [target ^ " = None"]
  | E_for (id, start, finish, step, Ord_aux (order, _), body) ->
      let before_start, start = lower_value ctx start in
      let before_finish, finish = lower_value ctx finish in
      let before_step, step = lower_value ctx step in
      let increasing = match order with Ord_inc -> "True" | Ord_dec -> "False" in
      before_start @ before_finish @ before_step
      @ block
          ("for " ^ safe_local_name id ^ " in sail_range(" ^ start ^ ", " ^ finish ^ ", " ^ step ^ ", " ^ increasing
         ^ "):"
          )
          (with_local_ids ctx [id] (fun () -> emit_stmt ctx body))
      @ [target ^ " = None"]
  | E_loop (While, _, condition, body) ->
      let before, condition = lower_value ctx condition in
      block "while True:" (before @ block ("if not (" ^ condition ^ "):") ["break"] @ emit_stmt ctx body)
      @ [target ^ " = None"]
  | E_loop (Until, _, condition, body) ->
      let before, condition = lower_value ctx condition in
      block "while True:" (emit_stmt ctx body @ before @ block ("if " ^ condition ^ ":") ["break"])
      @ [target ^ " = None"]
  | _ ->
      let before, value = lower_value ctx exp in
      before @ [target ^ " = " ^ value]

and emit_stmt ctx (E_aux (exp_aux, _) as exp) =
  match exp_aux with
  | E_assign (target, value) -> emit_assignment ctx target value
  | E_return value | E_internal_return value ->
      let before, value = lower_value ctx value in
      before @ ["raise SailReturn(" ^ value ^ ")"]
  | E_throw value ->
      let before, value = lower_value ctx value in
      before @ ["raise SailThrown(" ^ value ^ ")"]
  | E_exit value ->
      let before, value = lower_value ctx value in
      before @ ["raise SailExit(" ^ value ^ ")"]
  | _ -> emit_structural_stmt ctx exp

let typquant_comment typq =
  match typq with [] -> [] | _ -> ["# Sail type parameters: " ^ String.concat ", " (List.map (fun _ -> "...") typq)]

let record_field_has_validation ctx env typ =
  let typ = try Env.expand_synonyms env typ with Type_internal.Type_error _ -> typ in
  match fixed_bytes_type ctx typ with
  | Some _ -> false
  | None -> (
      match typ with
      | Typ_aux (Typ_id id, _) when id_string id = "nat" -> false
      | Typ_aux (Typ_app (id, [A_aux (A_nexp lower, _); A_aux (A_nexp upper, _)]), _) when id_string id = "range" -> (
          match (big_int_of_nexp lower, big_int_of_nexp upper) with
          | Some lower, Some _ when Big_int.less_equal Big_int.zero lower -> false
          | _ -> true
        )
      | Typ_aux (Typ_app (id, [_; _]), _) when id_string id = "vector" -> true
      | Typ_aux (Typ_app (id, [_]), _)
        when id_string id = "atom" || id_string id = "implicit" || id_string id = "itself" ->
          true
      | _ -> false
    )

let record_field_validation ctx env value typ =
  let typ = Env.expand_synonyms env typ in
  let required_bound description nexp = required_runtime_nexp ~loc:(typ_loc typ) ctx description nexp in
  match typ with
  | Typ_aux (Typ_id id, _) when id_string id = "nat" -> None
  | Typ_aux (Typ_app (id, [A_aux (A_nexp lower, _); A_aux (A_nexp upper, _)]), _) when id_string id = "range" -> (
      match (big_int_of_nexp lower, big_int_of_nexp upper) with
      | Some lower, Some _ when Big_int.less_equal Big_int.zero lower -> None
      | _ ->
          let lower = required_bound "record range lower bound" lower in
          let upper = required_bound "record range upper bound" upper in
          Some ("(" ^ lower ^ " <= int(" ^ value ^ ") <= " ^ upper ^ ")", string_of_typ typ)
    )
  | Typ_aux (Typ_app (id, [A_aux (A_nexp expected, _)]), _)
    when id_string id = "atom" || id_string id = "implicit" || id_string id = "itself" ->
      let expected = required_bound "record singleton value" expected in
      Some ("(int(" ^ value ^ ") == " ^ expected ^ ")", string_of_typ typ)
  | Typ_aux (Typ_app (id, [_]), _) when id_string id = "bitvector" || id_string id = "bits" -> None
  | Typ_aux (Typ_app (id, [A_aux (A_nexp length, _); A_aux (A_typ _, _)]), _) when id_string id = "vector" ->
      if Option.is_some (fixed_bytes_type ctx typ) then None
      else (
        let length = required_bound "record vector length" length in
        Some ("(len(" ^ value ^ ") == " ^ length ^ ")", string_of_typ typ)
      )
  | _ -> None

let pydantic_validator checks =
  match checks with
  | [] -> []
  | checks ->
      let body =
        concat_map
          (fun (condition, message) ->
            block ("if not (" ^ condition ^ "):") ["raise ValueError(" ^ py_string message ^ ")"]
          )
          checks
        @ ["return self"]
      in
      [""; "@model_validator(mode=\"after\")"] @ block "def validate(self) -> Self:" body

let record_field_type_alias owner annotation = "_" ^ owner ^ "_" ^ annotation ^ "_type"

let record_field_names fields =
  List.fold_left (fun names ((field, _), _) -> StringSet.add (py_id field) names) StringSet.empty fields

let record_field_type ctx owner field_names typ =
  let annotation = python_typ ctx typ in
  if StringSet.mem annotation field_names then record_field_type_alias owner annotation else annotation

let record_field_type_aliases ctx owner fields =
  let field_names = record_field_names fields in
  List.fold_left
    (fun aliases ((_, typ), _) ->
      let annotation = python_typ ctx typ in
      if StringSet.mem annotation field_names then StringSet.add annotation aliases else aliases
    )
    StringSet.empty fields
  |> StringSet.elements
  |> List.map (fun annotation -> record_field_type_alias owner annotation ^ ": TypeAlias = " ^ annotation)

let pydantic_record_definition ctx l id typq fields =
  let owner = type_name ctx id in
  let field_names = record_field_names fields in
  let env = Env.add_typquant l typq ctx.env in
  let quantifiers = runtime_quantifiers typq in
  let has_validity = quantifiers <> [] in
  let validity_lines =
    if not has_validity then []
    else (
      let validity = validity_type_name ctx id in
      let numeric_values =
        List.fold_left
          (fun values (kid, name, python_type) ->
            KBindings.add kid
              (runtime_numeric_value ~already_integer:(String.equal python_type "int") ("self." ^ name))
              values
          )
          KBindings.empty quantifiers
      in
      let checks =
        with_numeric_values ctx numeric_values (fun () ->
            typquant_constraints typq
            |> List.map (fun constraint_ ->
                ( required_runtime_constraint ~loc:l ctx env (owner ^ " validity") constraint_,
                  validity ^ " violates Sail constraint " ^ string_of_n_constraint constraint_
                )
            )
        )
      in
      let body =
        List.map (fun (_, name, python_type) -> name ^ ": " ^ python_type) quantifiers @ pydantic_validator checks
      in
      [
        "@pydantic_dataclass(config=ConfigDict(strict=True, arbitrary_types_allowed=True), frozen=True, slots=True, \
         kw_only=True)";
      ]
      @ block ("class " ^ validity ^ ":") body
      @ [""]
    )
  in
  let numeric_values =
    List.fold_left
      (fun values (kid, name, python_type) ->
        KBindings.add kid
          (runtime_numeric_value ~already_integer:(String.equal python_type "int") ("self.validity." ^ name))
          values
      )
      KBindings.empty quantifiers
  in
  let field_checks =
    with_numeric_values ctx numeric_values (fun () ->
        List.filter_map
          (fun ((field, typ), _) ->
            Option.map
              (fun (condition, sail_type) -> (condition, owner ^ "." ^ py_id field ^ " violates Sail type " ^ sail_type))
              (record_field_validation ctx env ("self." ^ py_id field) typ)
          )
          fields
    )
  in
  let body =
    (if has_validity then ["validity: " ^ validity_type_name ctx id] else [])
    @ List.map (fun ((field, typ), _) -> py_id field ^ ": " ^ record_field_type ctx owner field_names typ) fields
    @ pydantic_validator field_checks
  in
  validity_lines
  @ record_field_type_aliases ctx owner fields
  @ [
      "@pydantic_dataclass(config=ConfigDict(strict=True, validate_assignment=True, revalidate_instances=\"always\", \
       arbitrary_types_allowed=True), slots=True, kw_only=True)";
    ]
  @ block ("class " ^ owner ^ ":") body
  @ [""]

let type_definition ctx (TD_aux (definition, (l, _))) =
  match definition with
  | TD_record (id, typq, fields, _) ->
      let env = Env.add_typquant l typq ctx.env in
      let needs_validation =
        runtime_quantifiers typq <> []
        || List.exists (fun ((_, typ), _) -> record_field_has_validation ctx env typ) fields
      in
      if ctx.pydantic && needs_validation then pydantic_record_definition ctx l id typq fields
      else (
        let owner = type_name ctx id in
        let field_names = record_field_names fields in
        let body =
          typquant_comment typq
          @ List.map (fun ((field, typ), _) -> py_id field ^ ": " ^ record_field_type ctx owner field_names typ) fields
        in
        record_field_type_aliases ctx owner fields
        @ ("@dataclass(slots=True)" :: block ("class " ^ owner ^ ":") body)
        @ [""]
      )
  | TD_variant (id, _, _, _) when String.equal (id_string id) "option" ->
      [type_name ctx id ^ ": TypeAlias = Any | None"; ""]
  | TD_variant (id, typq, constructors, _) ->
      let owner = type_name ctx id in
      let env = Env.add_typquant l typq ctx.env in
      let base = block ("class " ^ owner ^ ":") (typquant_comment typq @ ["pass"]) @ [""] in
      let constructors =
        concat_map
          (fun (Tu_aux (Tu_ty_id (typ, constructor), _)) ->
            let field = if is_unit_typ env typ then "value: None = None" else "value: " ^ python_typ ctx typ in
            ["@dataclass(frozen=True, slots=True)"]
            @ block ("class " ^ constructor_name ctx constructor ^ "(" ^ owner ^ "):") [field]
            @ [""]
          )
          constructors
      in
      base @ constructors
  | TD_enum (id, members, _) ->
      let numeric = IdSet.mem id ctx.numeric_enums in
      let body =
        match members with
        | [] -> ["pass"]
        | _ when numeric ->
            List.mapi (fun index (member, _) -> py_id member ^ " = Uint(" ^ string_of_int index ^ ")") members
        | _ -> List.map (fun (member, _) -> py_id member ^ " = auto()") members
      in
      block ("class " ^ type_name ctx id ^ "(" ^ (if numeric then "UintEnum" else "Enum") ^ "):") body @ [""]
  | TD_abbrev (id, _, A_aux (A_typ typ, _)) -> (
      match range_bounds ctx.env typ with
      | Some (lower, upper) when Big_int.less_equal Big_int.zero lower && Option.is_none (public_uint_width lower upper)
        ->
          let body =
            [
              "LOWER = " ^ Big_int.to_string lower;
              "UPPER = " ^ Big_int.to_string upper;
              "";
              "def _in_range(self, value: int) -> bool:";
              "    return self.LOWER <= value <= self.UPPER";
            ]
          in
          block ("class " ^ type_name ctx id ^ "(Unsigned):") body @ [""]
      | _ -> [type_name ctx id ^ ": TypeAlias = " ^ python_alias_typ ctx typ; ""]
    )
  | TD_abbrev (_, _, _) -> []
  | TD_abstract (id, _, _) -> block ("class " ^ type_name ctx id ^ ":") ["pass"] @ [""]
  | TD_bitfield _ -> backend_error ~loc:l "bitfield type survived the Python rewrite pipeline"

let clause_parts = function
  | Pat_aux (Pat_exp (pat, body), _) -> (pat, None, body)
  | Pat_aux (Pat_when (pat, guard, body), _) -> (pat, Some guard, body)

let split_argument_patterns count pat =
  match (count, pat) with
  | 0, _ -> []
  | 1, P_aux (P_tuple [pat], _) -> [pat]
  | 1, pat -> [pat]
  | count, P_aux (P_tuple pats, _) when List.length pats = count -> pats
  | count, _ -> List.init count (fun _ -> pat)

let simple_parameter = function
  | P_aux (P_id id, _) -> Some (safe_local_name id)
  | P_aux (P_typ (_, P_aux (P_id id, _)), _) -> Some (safe_local_name id)
  | _ -> None

let add_numeric_value ?(already_integer = false) values kid expression =
  if KBindings.mem kid values then values
  else KBindings.add kid (runtime_numeric_value ~already_integer expression) values

let record_numeric_values ctx name values id args =
  match Bindings.find_opt id ctx.record_quants with
  | Some typq when record_has_validity ctx typq ->
      let rec collect values quantifiers args =
        match (quantifiers, args) with
        | [], [] -> values
        | ( KOpt_aux (KOpt_kind (K_aux (K_int, _), parameter), _) :: quantifiers,
            A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _) :: args ) ->
            collect
              (add_numeric_value ~already_integer:true values kid (name ^ ".validity." ^ kid_name parameter))
              quantifiers args
        | ( KOpt_aux (KOpt_kind (K_aux (K_bool, _), parameter), _) :: quantifiers,
            A_aux (A_bool (NC_aux (NC_var kid, _)), _) :: args ) ->
            collect (add_numeric_value values kid (name ^ ".validity." ^ kid_name parameter)) quantifiers args
        | KOpt_aux (KOpt_kind (K_aux (K_type, _), _), _) :: quantifiers, A_aux (A_typ _, _) :: args
        | _ :: quantifiers, _ :: args ->
            collect values quantifiers args
        | _ -> values
      in
      collect values (quant_kopts typq) args
  | _ -> values

let rec numeric_values_from_parameter ctx env name values typ =
  match Env.expand_synonyms env typ with
  | Typ_aux
      ( Typ_app
          (id, [A_aux (A_nexp (Nexp_aux (Nexp_var lower, _)), _); A_aux (A_nexp (Nexp_aux (Nexp_var upper, _)), _)]),
        _
      )
    when id_string id = "range" && Kid.compare lower upper = 0 ->
      add_numeric_value values lower name
  | Typ_aux (Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _)]), _)
    when id_string id = "atom" || id_string id = "implicit" || id_string id = "itself" ->
      add_numeric_value values kid name
  | Typ_aux (Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _)]), _)
    when id_string id = "bitvector" || id_string id = "bits" ->
      add_numeric_value ~already_integer:true values kid ("len(" ^ name ^ ")")
  | Typ_aux (Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _); A_aux (A_typ _, _)]), _)
    when id_string id = "vector" ->
      add_numeric_value ~already_integer:true values kid ("len(" ^ name ^ ")")
  | Typ_aux (Typ_app (id, args), _) when IdSet.mem id ctx.records -> record_numeric_values ctx name values id args
  | Typ_aux (Typ_exist (_, _, body), _) -> numeric_values_from_parameter ctx env name values body
  | _ -> values

let numeric_values_of_parameters ctx env parameters =
  List.fold_left
    (fun values (name, typ) -> numeric_values_from_parameter ctx env name values typ)
    KBindings.empty parameters

let written_registers exp =
  let le_aux ((registers, lexp), annot) =
    let registers =
      match lexp with
      | LE_id id | LE_typ (_, id) -> (
          match Env.lookup_id id (env_of_annot annot) with
          | Register _ -> IdSet.add id registers
          | Local _ | Enum _ | Unbound _ -> registers
        )
      | _ -> registers
    in
    (registers, LE_aux (lexp, annot))
  in
  fst (Rewriter.fold_exp { (Rewriter.compute_exp_alg IdSet.empty IdSet.union) with le_aux } exp)

let combined_pattern ctx patterns =
  let patterns = List.map (python_pat ctx) patterns in
  match patterns with
  | [] -> ("_", [], true)
  | [pattern] -> (pattern.pattern, pattern.guards, pattern.irrefutable)
  | patterns ->
      ( "(" ^ String.concat ", " (List.map (fun pattern -> pattern.pattern) patterns) ^ ")",
        concat_map (fun pattern -> pattern.guards) patterns,
        List.for_all (fun pattern -> pattern.irrefutable) patterns
      )

let function_lines ~preserve_structure ctx (FD_aux (FD_function (_, _, clauses), _)) =
  match clauses with
  | [] -> []
  | FCL_aux (FCL_funcl (id, _), _) :: _ when Bindings.mem id ctx.externs -> []
  | FCL_aux (FCL_funcl (id, first_clause), _) :: _ ->
      let arg_types, result_type =
        match function_type ctx id with
        | Some signature -> signature
        | None -> backend_error ("function " ^ id_string id ^ " has no function val specification")
      in
      let first_pat, _, first_body = clause_parts first_clause in
      let env = env_of first_body in
      let unit_function = match arg_types with [typ] -> is_unit_typ env typ | _ -> false in
      let public_arg_types = if unit_function then [] else arg_types in
      let first_patterns = split_argument_patterns (List.length public_arg_types) first_pat in
      let single_clause = List.length clauses = 1 in
      let parameters =
        List.mapi
          (fun index typ ->
            let name =
              if single_clause then
                Option.value
                  (Option.bind (List.nth_opt first_patterns index) simple_parameter)
                  ~default:(Printf.sprintf "_arg%d" index)
              else Printf.sprintf "_arg%d" index
            in
            (name, typ)
          )
          public_arg_types
      in
      let hidden_parameters =
        let used = ref (StringSet.of_list (List.map fst parameters)) in
        List.map
          (fun (kid, name, python_type) ->
            let name = choose_name used ("_sail_implicit_" ^ name) ("_sail_implicit_" ^ name) in
            (kid, name, python_type)
          )
          (function_hidden_quantifiers ctx env id)
      in
      let previous_numeric_values = ctx.numeric_values in
      let previous_return_constructor = ctx.current_return_constructor in
      ctx.numeric_values <-
        List.fold_left
          (fun values (kid, name, _) -> KBindings.add kid (runtime_numeric_value name) values)
          (numeric_values_of_parameters ctx env parameters)
          hidden_parameters;
      ctx.current_return_constructor <- constructor_for_function ctx env id result_type;
      let header =
        "def " ^ value_name ctx id ^ "("
        ^ String.concat ", "
            (List.map (fun (name, typ) -> name ^ ": " ^ python_typ ctx typ) parameters
            @ List.map (fun (_, name, python_type) -> name ^ ": " ^ python_type) hidden_parameters
            )
        ^ ") -> " ^ python_typ ctx result_type ^ ":"
      in
      let written_registers, has_early_return =
        List.fold_left
          (fun (registers, has_return) (FCL_aux (FCL_funcl (_, clause), _)) ->
            let _, guard, body = clause_parts clause in
            let registers = IdSet.union registers (written_registers body) in
            let registers =
              match guard with None -> registers | Some guard -> IdSet.union registers (written_registers guard)
            in
            (registers, has_return || Rewriter.has_early_return body)
          )
          (IdSet.empty, false) clauses
      in
      let globals =
        let written_registers =
          match ctx.current_module with
          | None -> written_registers
          | Some current_module ->
              IdSet.filter
                (fun id ->
                  match Bindings.find_opt id ctx.register_modules with
                  | Some owner -> same_module current_module owner
                  | None -> false
                )
                written_registers
        in
        if IdSet.is_empty written_registers then []
        else ["global " ^ String.concat ", " (List.map (value_name ctx) (IdSet.elements written_registers))]
      in
      let conservative_body result =
        if single_clause then (
          let pat, guard, exp = clause_parts first_clause in
          let patterns = split_argument_patterns (List.length public_arg_types) pat in
          let local_ids = concat_map bound_ids patterns in
          let binds =
            List.fold_left2
              (fun lines pattern (parameter, _) ->
                match simple_parameter pattern with
                | Some name when String.equal name parameter -> lines
                | _ -> lines @ emit_pattern_scope ctx parameter pattern []
              )
              [] patterns parameters
          in
          let guarded_body =
            with_local_ids ctx local_ids (fun () ->
                with_patterns_numeric_values ctx patterns (fun () ->
                    match guard with
                    | None -> emit_into ctx result exp
                    | Some guard ->
                        let before, guard = lower_value ctx guard in
                        before
                        @ block ("if " ^ guard ^ ":") (emit_into ctx result exp)
                        @ block "else:"
                            ["raise SailMatchFailure(" ^ py_string ("function clause for " ^ id_string id) ^ ")"]
                )
            )
          in
          binds @ guarded_body
        )
        else (
          let scrutinee =
            match parameters with
            | [] -> "None"
            | [(name, _)] -> name
            | _ -> "(" ^ String.concat ", " (List.map fst parameters) ^ ")"
          in
          let pexps = List.map (fun (FCL_aux (FCL_funcl (_, clause), _)) -> clause) clauses in
          emit_cases ctx result scrutinee pexps
            ["raise SailMatchFailure(" ^ py_string ("no clause of " ^ id_string id ^ " matched") ^ ")"]
        )
      in
      let structural_body () =
        if single_clause then (
          let pat, guard, exp = clause_parts first_clause in
          let patterns = split_argument_patterns (List.length public_arg_types) pat in
          with_local_ids ctx (concat_map bound_ids patterns) (fun () ->
              with_patterns_numeric_values ctx patterns (fun () ->
                  let all_simple =
                    List.for_all2
                      (fun pattern (parameter, _) ->
                        match simple_parameter pattern with Some name -> String.equal name parameter | None -> false
                      )
                      patterns parameters
                  in
                  let guarded_body guards =
                    match guards with
                    | [] -> emit_return ctx result_type exp
                    | guards ->
                        block ("if " ^ String.concat " and " guards ^ ":") (emit_return ctx result_type exp)
                        @ block "else:"
                            ["raise SailMatchFailure(" ^ py_string ("function clause for " ^ id_string id) ^ ")"]
                  in
                  let explicit_guard =
                    match guard with
                    | None -> []
                    | Some guard ->
                        let before, guard = lower_value ctx guard in
                        if before <> [] then backend_error "effectful function guard survived expression lifting";
                        [guard]
                  in
                  if all_simple then guarded_body explicit_guard
                  else (
                    let scrutinee =
                      match parameters with
                      | [] -> "None"
                      | [(name, _)] -> name
                      | _ -> "(" ^ String.concat ", " (List.map fst parameters) ^ ")"
                    in
                    let pattern, pattern_guards, _ = combined_pattern ctx patterns in
                    block
                      ("match " ^ scrutinee ^ ":")
                      (block
                         ("case " ^ pattern ^ guard_clause (pattern_guards @ explicit_guard) ^ ":")
                         (emit_return ctx result_type exp)
                      @ block "case _:"
                          ["raise SailMatchFailure(" ^ py_string ("function clause for " ^ id_string id) ^ ")"]
                      )
                  )
              )
          )
        )
        else (
          let scrutinee =
            match parameters with
            | [] -> "None"
            | [(name, _)] -> name
            | _ -> "(" ^ String.concat ", " (List.map fst parameters) ^ ")"
          in
          let pexps = List.map (fun (FCL_aux (FCL_funcl (_, clause), _)) -> clause) clauses in
          emit_return_cases ctx result_type scrutinee pexps
            ["raise SailMatchFailure(" ^ py_string ("no clause of " ^ id_string id ^ " matched") ^ ")"]
        )
      in
      let lines =
        if preserve_structure then (
          let structural_body = structural_body () in
          let body =
            if has_early_return then
              block "try:" structural_body
              @ block "except SailReturn as _sail_return:" ["return " ^ return_value ctx "_sail_return.value"]
            else structural_body
          in
          block header (globals @ body) @ [""]
        )
        else (
          let result = fresh ctx "result" in
          let body = conservative_body result in
          let catch =
            if has_early_return then
              block "try:" body @ block "except SailReturn as _sail_return:" [result ^ " = _sail_return.value"]
            else body
          in
          let return = "return " ^ return_value ctx result in
          block header (globals @ catch @ [return]) @ [""]
        )
      in
      ctx.numeric_values <- previous_numeric_values;
      ctx.current_return_constructor <- previous_return_constructor;
      lines

let function_definition ~preserve_structure ctx = function
  | DEF_aux (DEF_fundef function_definition, _) ->
      in_function_body (fun () -> function_lines ~preserve_structure ctx function_definition)
  | DEF_aux (DEF_internal_mutrec definitions, _) ->
      in_function_body (fun () -> concat_map (function_lines ~preserve_structure ctx) definitions)
  | _ -> []

let register_declarations ctx defs =
  let declarations =
    List.fold_left
      (fun declarations (DEF_aux (definition, _)) ->
        match definition with
        | DEF_register (DEC_aux (DEC_reg (typ, id, _), _)) ->
            declarations @ [value_name ctx id ^ ": " ^ python_typ ctx typ]
        | _ -> declarations
      )
      [] defs
  in
  if declarations = [] then [] else declarations @ [""]

let top_level_let_definition ctx pat exp =
  let before, value = lower_value ctx exp in
  let annotations = List.map (fun (id, typ) -> value_name ctx id ^ ": " ^ python_typ ctx typ) (bound_id_typs pat) in
  match (bound_id_typs pat, assignment_pattern ctx pat, before) with
  | [(id, typ)], Some target, [] when String.equal target (value_name ctx id) ->
      [target ^ ": " ^ python_typ ctx typ ^ " = " ^ construct_value ctx (env_of exp) typ value]
  | [], Some "_", [] -> ["_ = " ^ value]
  | _ -> annotations @ before @ emit_pattern_scope ctx value pat []

let top_level_let_definitions ctx defs =
  let definitions =
    concat_map
      (fun (DEF_aux (definition, _)) ->
        match definition with DEF_let (pat, exp) -> top_level_let_definition ctx pat exp | _ -> []
      )
      defs
  in
  if definitions = [] then [] else definitions @ [""]

let register_initial_value ctx typ initial =
  match initial with
  | Some initial -> lower_value ctx initial
  | None -> ([], "sail_default(" ^ py_string (python_typ ctx typ) ^ ")")

let source_register_definition ctx typ id initial =
  let before, initial = register_initial_value ctx typ initial in
  before @ [value_name ctx id ^ ": " ^ python_typ ctx typ ^ " = " ^ initial; ""]

let source_state_definition ctx = function
  | DEF_aux (DEF_let (pat, exp), _) -> top_level_let_definition ctx pat exp @ [""]
  | DEF_aux (DEF_register (DEC_aux (DEC_reg (typ, id, initial), _)), _) -> source_register_definition ctx typ id initial
  | _ -> []

let source_reset_function ctx definitions =
  let registers =
    List.filter_map
      (fun (DEF_aux (definition, _)) ->
        match definition with
        | DEF_register (DEC_aux (DEC_reg (typ, id, initial), _)) -> Some (typ, id, initial)
        | _ -> None
      )
      definitions
  in
  match registers with
  | [] -> []
  | registers ->
      let globals = List.map (fun (_, id, _) -> value_name ctx id) registers in
      let assignments =
        concat_map
          (fun (typ, id, initial) ->
            let before, initial = register_initial_value ctx typ initial in
            before @ [value_name ctx id ^ " = " ^ initial]
          )
          registers
      in
      block "def _reset_registers() -> None:" (["global " ^ String.concat ", " globals] @ assignments @ ["return None"])
      @ [""]

let source_order_definition ctx definition =
  match definition with
  | DEF_aux (DEF_type definition, _) -> type_definition ctx definition
  | DEF_aux (DEF_fundef _, _) | DEF_aux (DEF_internal_mutrec _, _) ->
      function_definition ~preserve_structure:true ctx definition
  | DEF_aux (DEF_let (pat, exp), _) -> top_level_let_definition ctx pat exp @ [""]
  | DEF_aux (DEF_register (DEC_aux (DEC_reg (typ, id, _), _)), _) -> [value_name ctx id ^ ": " ^ python_typ ctx typ; ""]
  | _ -> []

let reset_function ctx defs =
  let globals = IdSet.elements ctx.registers in
  let global_line =
    match globals with [] -> [] | _ -> ["global " ^ String.concat ", " (List.map (value_name ctx) globals)]
  in
  let body =
    List.fold_left
      (fun lines (DEF_aux (definition, _)) ->
        match definition with
        | DEF_register (DEC_aux (DEC_reg (typ, id, initial), _)) ->
            let before, initial =
              match initial with
              | Some initial -> lower_value ctx initial
              | None -> ([], "sail_default(" ^ py_string (python_typ ctx typ) ^ ")")
            in
            lines @ before @ [value_name ctx id ^ " = " ^ initial]
        | _ -> lines
      )
      [] defs
  in
  block "def reset() -> None:" (global_line @ body @ ["return None"])
  @ [""; "def finish() -> None:"; "    return None"; ""]

let metadata_dictionary name entries =
  match entries with
  | [] -> [name ^ " = {}"]
  | _ -> [name ^ " = {"] @ List.map (fun entry -> "    " ^ entry ^ ",") entries @ ["}"]

let metadata ctx effect_info defs =
  let types =
    List.filter_map
      (fun (DEF_aux (definition, _)) ->
        match definition with
        | DEF_type (TD_aux (type_definition, _)) -> (
            match type_definition with
            | TD_record (id, _, _, _) | TD_variant (id, _, _, _) | TD_enum (id, _, _) | TD_abstract (id, _, _) ->
                Some (py_string (id_string id) ^ ": " ^ type_name ctx id)
            | TD_abbrev (id, _, A_aux (A_typ _, _)) -> Some (py_string (id_string id) ^ ": " ^ type_name ctx id)
            | TD_abbrev _ -> None
            | TD_bitfield _ -> None
          )
        | _ -> None
      )
      defs
  in
  let function_entry = function
    | FD_aux (FD_function (_, _, FCL_aux (FCL_funcl (id, _), _) :: _), _) when not (Bindings.mem id ctx.externs) ->
        Some (py_string (id_string id) ^ ": " ^ value_name ctx id)
    | _ -> None
  in
  let functions =
    concat_map
      (fun (DEF_aux (definition, _)) ->
        match definition with
        | DEF_fundef function_definition -> Option.to_list (function_entry function_definition)
        | DEF_internal_mutrec function_definitions -> List.filter_map function_entry function_definitions
        | _ -> []
      )
      defs
  in
  let source_signatures, effects, external_targets =
    List.fold_left
      (fun (signatures, effects, external_targets) (DEF_aux (definition, _)) ->
        match definition with
        | DEF_val (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ), _), id, _), _)) ->
            let name = py_string (id_string id) in
            let signature = string_of_typquant typq ^ ". " ^ string_of_typ typ in
            let signatures = signatures @ [name ^ ": " ^ py_string signature] in
            let purity = if Effects.function_is_pure id effect_info then "pure" else "effectful" in
            let effects = effects @ [name ^ ": " ^ py_string purity] in
            let external_targets =
              match Bindings.find_opt id ctx.externs with
              | Some target -> external_targets @ [name ^ ": " ^ py_string target]
              | None -> external_targets
            in
            (signatures, effects, external_targets)
        | _ -> (signatures, effects, external_targets)
      )
      ([], [], []) defs
  in
  metadata_dictionary "__sail_types__" types
  @ metadata_dictionary "__sail_functions__" functions
  @ ["__sail_signatures__ = {name: function.__annotations__ for name, function in __sail_functions__.items()}"]
  @ metadata_dictionary "__sail_source_signatures__" source_signatures
  @ metadata_dictionary "__sail_effects__" effects
  @ metadata_dictionary "__sail_externs__" external_targets
  @ [""]

type generated_file = { relative_path : string; contents : string }

let generated_banner = "# Generated by Sail's Python backend. Do not edit by hand."

let explicit_import ?(reexport = false) module_name names =
  match names with
  | [] -> []
  | names ->
      ["from " ^ module_name ^ " import ("]
      @ List.map (fun name -> "    " ^ name ^ (if reexport then " as " ^ name else "") ^ ",") names
      @ [")"]

let python_identifier_character = function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false

let line_uses_identifier line name =
  let line_length = String.length line in
  let name_length = String.length name in
  let rec search index =
    if index + name_length > line_length then false
    else if String.sub line index name_length <> name then search (index + 1)
    else (
      let starts_identifier = index = 0 || not (python_identifier_character line.[index - 1]) in
      let finish = index + name_length in
      let ends_identifier = finish = line_length || not (python_identifier_character line.[finish]) in
      if starts_identifier && ends_identifier then true else search (index + 1)
    )
  in
  name_length > 0 && search 0

let imports_used_by lines candidates =
  List.filter (fun name -> List.exists (fun line -> line_uses_identifier line name) lines) candidates

let extern_imports_for module_name ctx lines =
  let imports =
    Bindings.fold
      (fun _ target imports ->
        let imported = python_identifier target in
        let binding = extern_binding_name target in
        if List.exists (fun line -> line_uses_identifier line binding) lines then StringMap.add imported binding imports
        else imports
      )
      ctx.externs StringMap.empty
    |> StringMap.bindings
  in
  match imports with
  | [] -> []
  | imports ->
      ["from " ^ module_name ^ " import ("]
      @ List.map (fun (imported, binding) -> "    " ^ imported ^ " as " ^ binding ^ ",") imports
      @ [")"]

let python_imports_for lines =
  let support_import module_name candidates =
    match imports_used_by lines candidates with
    | [] -> []
    | names -> ["from " ^ module_name ^ " import " ^ String.concat ", " names]
  in
  support_import "copy" ["deepcopy"]
  @ support_import "dataclasses" ["dataclass"; "replace"]
  @ support_import "enum" ["Enum"; "auto"]
  @ support_import "typing" ["Annotated"; "Any"; "Callable"; "TypeAlias"]
  @ support_import "pydantic" ["ConfigDict"; "ValidationInfo"; "field_validator"; "model_validator"]
  @ ( if List.exists (fun line -> line_uses_identifier line "pydantic_dataclass") lines then
        ["from pydantic.dataclasses import dataclass as pydantic_dataclass"]
      else []
    )
  @ support_import "typing_extensions" ["Self"]

let fixed_bytes_python_types ctx =
  IntMap.bindings ctx.fixed_bytes_types |> List.map snd |> List.sort_uniq String.compare

let ethereum_types_runtime_names ctx =
  ["U8"; "U16"; "U32"; "U64"; "U256"; "Uint"; "UintEnum"; "Unsigned"] @ fixed_bytes_python_types ctx
  |> StringSet.of_list

let profile_runtime_import_names ctx names =
  match ctx.extern_module with
  | Some _ -> List.filter (fun name -> not (StringSet.mem name extern_registry_runtime_names)) names
  | None -> names

let context_runtime_import_names ctx =
  runtime_import_names ~external_names:(fixed_bytes_python_types ctx) () |> profile_runtime_import_names ctx

let ethereum_types_import module_name names =
  String.concat "\n"
    (["from ethereum_types." ^ module_name ^ " import ("]
    @ List.map (fun name -> "    " ^ name ^ " as " ^ name ^ ",") names
    @ [")"]
    )

let ethereum_types_import_source ctx =
  let numeric_imports =
    [
      ethereum_types_import "numeric" ["U8"; "U16"; "U32"; "U64"; "U256"; "Uint"; "Unsigned"];
      ethereum_types_import "enum" ["UintEnum"];
    ]
  in
  let byte_imports =
    match fixed_bytes_python_types ctx with [] -> [] | names -> [ethereum_types_import "bytes" names]
  in
  String.concat "\n"
    (numeric_imports @ byte_imports @ [""; "_FIXED_UINTS = {8: U8, 16: U16, 32: U32, 64: U64, 256: U256}"])

let runtime_profile_import_marker =
  "from ethereum_types.numeric import Unsigned  # __SAIL_PYTHON_RUNTIME_PROFILE_IMPORTS__"
let generic_numeric_start_marker = "# __SAIL_GENERIC_NUMERIC_START__"
let generic_numeric_end_marker = "# __SAIL_GENERIC_NUMERIC_END__"
let extern_registry_start_marker = "# __SAIL_EXTERN_REGISTRY_START__"
let extern_registry_end_marker = "# __SAIL_EXTERN_REGISTRY_END__"

let inject_runtime_profile_imports runtime imports =
  runtime |> String.split_on_char '\n'
  |> List.map (fun line -> if String.equal line runtime_profile_import_marker then imports else line)
  |> String.concat "\n"

let remove_marked_section runtime start_marker end_marker =
  let rec remove inside = function
    | [] -> []
    | line :: lines when String.equal line start_marker -> remove true lines
    | line :: lines when String.equal line end_marker -> remove false lines
    | _ :: lines when inside -> remove true lines
    | line :: lines -> line :: remove false lines
  in
  runtime |> String.split_on_char '\n' |> remove false |> String.concat "\n"

let runtime_source ctx runtime_module =
  let imports = ethereum_types_import_source ctx in
  let runtime =
    match runtime_module with
    | None ->
        let runtime = inject_runtime_profile_imports Python_runtime_embedded.source imports in
        let runtime = remove_marked_section runtime generic_numeric_start_marker generic_numeric_end_marker in
        if Option.is_some ctx.extern_module then
          remove_marked_section runtime extern_registry_start_marker extern_registry_end_marker
        else runtime
    | Some module_name ->
        let external_runtime_imports =
          context_runtime_import_names ctx
          |> List.filter (fun name -> not (StringSet.mem name (ethereum_types_runtime_names ctx)))
        in
        String.concat "\n"
          (List.filter
             (fun source -> not (String.equal source ""))
             [imports; String.concat "\n" (explicit_import ~reexport:true module_name external_runtime_imports)]
          )
        ^ "\n"
  in
  runtime

let emitted_type_names ctx (TD_aux (definition, _)) =
  match definition with
  | TD_record (id, typq, _, _) ->
      let owner = binding_name ctx.type_names py_id id in
      if record_has_validity ctx typq then
        [owner; binding_name ctx.record_validity_names (fun id -> py_id id ^ "Validity") id]
      else [owner]
  | TD_enum (id, _, _) | TD_abstract (id, _, _) -> [binding_name ctx.type_names py_id id]
  | TD_variant (id, _, _, _) when String.equal (id_string id) "option" -> [binding_name ctx.type_names py_id id]
  | TD_variant (id, _, constructors, _) ->
      binding_name ctx.type_names py_id id
      :: List.map
           (fun (Tu_aux (Tu_ty_id (_, constructor), _)) ->
             binding_name ctx.constructor_names safe_value_name constructor
           )
           constructors
  | TD_abbrev (id, _, A_aux (A_typ _, _)) -> [binding_name ctx.type_names py_id id]
  | TD_abbrev _ | TD_bitfield _ -> []

let emitted_type_import_names ctx defs =
  concat_map
    (fun (DEF_aux (definition, _)) ->
      match definition with DEF_type definition -> emitted_type_names ctx definition | _ -> []
    )
    defs
  |> List.sort_uniq String.compare

let is_source_definition = function
  | DEF_aux ((DEF_type _ | DEF_fundef _ | DEF_internal_mutrec _ | DEF_let _ | DEF_register _), _) -> true
  | _ -> false

let function_ids = function
  | DEF_aux (DEF_fundef definition, _) -> [id_of_fundef definition]
  | DEF_aux (DEF_internal_mutrec definitions, _) -> List.map id_of_fundef definitions
  | _ -> []

let add_source_definition source definition groups =
  let rec add = function
    | [] -> [(source, [definition])]
    | (existing, definitions) :: groups when String.equal source existing ->
        (existing, definitions @ [definition]) :: groups
    | group :: groups -> group :: add groups
  in
  add groups

let source_definition_groups defs =
  let rec collect stack groups = function
    | [] -> groups
    | DEF_aux (DEF_pragma (("include_start" | "file_start"), Pragma_line (file, _)), _) :: defs
      when Filename.check_suffix file ".sail" ->
        collect (file :: stack) groups defs
    | DEF_aux (DEF_pragma (("include_end" | "file_end"), Pragma_line (file, _)), _) :: defs
      when Filename.check_suffix file ".sail" ->
        let stack = match stack with _ :: rest -> rest | [] -> [] in
        collect stack groups defs
    | definition :: defs when is_source_definition definition ->
        let source = match stack with file :: _ -> file | [] -> "main.sail" in
        collect stack (add_source_definition source definition groups) defs
    | _ :: defs -> collect stack groups defs
  in
  collect [] [] defs

let canonical_path path =
  let path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path in
  try Unix.realpath path with Unix.Unix_error _ -> path

let path_has_prefix ~prefix path =
  let prefix_length = String.length prefix in
  String.length path > prefix_length && String.sub path 0 prefix_length = prefix && Char.equal path.[prefix_length] '/'

let source_relative_path source_root source =
  match source_root with
  | None -> Filename.basename source
  | Some root ->
      let root = canonical_path root in
      let source = canonical_path source in
      if String.equal root source then Filename.basename source
      else if path_has_prefix ~prefix:root source then
        String.sub source (String.length root + 1) (String.length source - String.length root - 1)
      else Filename.concat "_sail" (Filename.basename source)

let package_component value =
  let value = python_identifier value in
  match value with "__init__" | "_runtime" | "_types" -> "sail_" ^ value | _ -> value

let module_components source_root source =
  let relative = source_relative_path source_root source in
  let without_extension =
    if Filename.check_suffix relative ".sail" then Filename.chop_suffix relative ".sail" else relative
  in
  String.split_on_char '/' without_extension
  |> List.filter (fun component -> (not (String.equal component "")) && not (String.equal component "."))
  |> List.map package_component
  |> function
  | [] -> ["main"]
  | components -> components

let unique_module_components source_root groups =
  let rec choose used components index =
    let candidate =
      if index = 0 then components
      else (
        match List.rev components with
        | leaf :: parents -> List.rev ((leaf ^ "_" ^ string_of_int index) :: parents)
        | [] -> ["main_" ^ string_of_int index]
      )
    in
    let key = module_key candidate in
    if StringSet.mem key used then choose used components (index + 1) else (StringSet.add key used, candidate)
  in
  let _, modules =
    List.fold_left
      (fun (used, modules) (source, definitions) ->
        let used, components = choose used (module_components source_root source) 0 in
        (used, modules @ [(source, components, definitions)])
      )
      (StringSet.empty, []) groups
  in
  modules

let dotted_module components = String.concat "." components

let module_file components = String.concat Filename.dir_sep components ^ ".py"

let emitted_function_ids ctx definitions =
  concat_map function_ids definitions |> List.filter (fun id -> not (Bindings.mem id ctx.externs))

let top_level_let_ids = function DEF_aux (DEF_let (pat, _), _) -> bound_ids pat | _ -> []

let emitted_value_ids ctx definitions = emitted_function_ids ctx definitions @ concat_map top_level_let_ids definitions

let type_module_bindings modules =
  List.fold_left
    (fun bindings (_, components, definitions) ->
      List.fold_left
        (fun bindings (DEF_aux (definition, _)) ->
          match definition with
          | DEF_type
              (TD_aux
                 ( ( TD_abbrev (id, _, _)
                   | TD_record (id, _, _, _)
                   | TD_variant (id, _, _, _)
                   | TD_enum (id, _, _)
                   | TD_abstract (id, _, _)
                   | TD_bitfield (id, _, _) ),
                   _
                 )
                ) ->
              Bindings.add id components bindings
          | _ -> bindings
        )
        bindings definitions
    )
    Bindings.empty modules

let value_module_bindings modules =
  List.fold_left
    (fun bindings (_, components, definitions) ->
      List.fold_left
        (fun bindings id -> Bindings.add id components bindings)
        bindings
        (concat_map function_ids definitions @ concat_map top_level_let_ids definitions)
    )
    Bindings.empty modules

let register_module_bindings modules =
  List.fold_left
    (fun bindings (_, components, definitions) ->
      List.fold_left
        (fun bindings (DEF_aux (definition, _)) ->
          match definition with
          | DEF_register (DEC_aux (DEC_reg (_, id, _), _)) -> Bindings.add id components bindings
          | _ -> bindings
        )
        bindings definitions
    )
    Bindings.empty modules

let bound_value_ids definitions =
  let add_ids ids bound = List.fold_left (fun ids id -> IdSet.add id ids) ids bound in
  let base = Rewriter.compute_exp_alg IdSet.empty IdSet.union in
  let pat_alg =
    {
      base.pat_alg with
      p_aux =
        (fun ((ids, pat_aux), annot) ->
          let pat = P_aux (pat_aux, annot) in
          (add_ids ids (bound_ids pat), pat)
        );
    }
  in
  let e_for ((id, _, _, _, _, _) as args) =
    let ids, exp_aux = base.e_for args in
    (IdSet.add id ids, exp_aux)
  in
  let le_aux ((ids, lexp_aux), annot) =
    let lexp = LE_aux (lexp_aux, annot) in
    (add_ids ids (lexp_bound_ids lexp), lexp)
  in
  let alg = { base with e_for; le_aux; pat_alg } in
  let add_function ids (FD_aux (FD_function (_, _, clauses), _) as function_definition) =
    List.fold_left
      (fun ids (FCL_aux (FCL_funcl (_, pexp), _)) ->
        let clause_ids, _ = Rewriter.fold_pexp alg pexp in
        IdSet.union ids clause_ids
      )
      (IdSet.add (id_of_fundef function_definition) ids)
      clauses
  in
  List.fold_left
    (fun ids (DEF_aux (definition, _)) ->
      match definition with
      | DEF_fundef function_definition -> add_function ids function_definition
      | DEF_internal_mutrec function_definitions -> List.fold_left add_function ids function_definitions
      | DEF_let (pat, _) -> add_ids ids (bound_ids pat)
      | DEF_register (DEC_aux (DEC_reg (_, id, _), _)) -> IdSet.add id ids
      | _ -> ids
    )
    IdSet.empty definitions

let bound_value_names definitions =
  IdSet.fold (fun id names -> StringSet.add (safe_value_name id) names) (bound_value_ids definitions) StringSet.empty

let value_import_name_bindings ctx type_import_names modules =
  let type_names = StringSet.of_list type_import_names in
  let bindings_for_module current_components definitions =
    let used = ref (StringSet.union runtime_names type_names) in
    used := StringSet.union !used (bound_value_names definitions);
    List.fold_left
      (fun names (_, target_components, target_definitions) ->
        if same_module current_components target_components then names
        else
          List.fold_left
            (fun names id ->
              let preferred = value_name ctx id in
              let qualified = String.concat "_" (target_components @ [preferred]) in
              let name = choose_name used preferred qualified in
              Bindings.add id name names
            )
            names
            (emitted_value_ids ctx target_definitions)
      )
      Bindings.empty modules
  in
  List.fold_left
    (fun bindings (_, components, definitions) ->
      StringMap.add (module_key components) (bindings_for_module components definitions) bindings
    )
    StringMap.empty modules

let module_import_name_bindings ctx type_import_names value_import_names modules =
  let type_names = StringSet.of_list type_import_names in
  let bindings_for_module current_components definitions =
    let used = ref (StringSet.union runtime_names type_names) in
    used := StringSet.union !used (bound_value_names definitions);
    ( match StringMap.find_opt (module_key current_components) value_import_names with
    | Some names -> Bindings.iter (fun _ name -> used := StringSet.add name !used) names
    | None -> ()
    );
    List.fold_left
      (fun names (_, target_components, _) ->
        if same_module current_components target_components then names
        else (
          let preferred = match List.rev target_components with leaf :: _ -> leaf | [] -> "source_module" in
          let qualified = String.concat "_" target_components in
          let name = choose_name used preferred qualified in
          StringMap.add (module_key target_components) name names
        )
      )
      StringMap.empty modules
  in
  List.fold_left
    (fun bindings (_, components, definitions) ->
      StringMap.add (module_key components) (bindings_for_module components definitions) bindings
    )
    StringMap.empty modules

let source_dependency_import package_name ctx current_components target_components type_names ids =
  let module_name = String.concat "." (package_name :: target_components) in
  let imported_name id =
    let original = value_name ctx id in
    let local = imported_value_name ctx current_components id in
    if String.equal original local then original else original ^ " as " ^ local
  in
  match type_names @ List.map imported_name ids with
  | [] -> []
  | [name] -> ["from " ^ module_name ^ " import " ^ name]
  | names -> ["from " ^ module_name ^ " import ("] @ List.map (fun name -> "    " ^ name ^ ",") names @ [")"]

let source_module_dependency_imports package_name ctx modules current_components referenced_type_names referenced_values
    =
  concat_map
    (fun (_, target_components, definitions) ->
      if same_module current_components target_components then []
      else (
        let type_names =
          emitted_type_import_names ctx definitions |> List.filter (fun name -> StringSet.mem name referenced_type_names)
        in
        let ids = emitted_value_ids ctx definitions |> List.filter (fun id -> IdSet.mem id referenced_values) in
        source_dependency_import package_name ctx current_components target_components type_names ids
      )
    )
    modules

let source_register_module_import package_name ctx current_components target_components =
  let local = imported_module_name ctx current_components target_components in
  match List.rev target_components with
  | leaf :: reversed_parents ->
      let parent_components = package_name :: List.rev reversed_parents in
      let parent = String.concat "." parent_components in
      let binding = if String.equal leaf local then leaf else leaf ^ " as " ^ local in
      ["from " ^ parent ^ " import " ^ binding]
  | [] -> []

let source_register_module_imports package_name ctx modules current_components referenced_modules =
  concat_map
    (fun (_, target_components, _) ->
      if
        same_module current_components target_components
        || not (StringSet.mem (module_key target_components) referenced_modules)
      then []
      else source_register_module_import package_name ctx current_components target_components
    )
    modules

type alias_dependencies = { names : StringSet.t; references : StringSet.t }

let alias_dependencies ctx = function
  | DEF_aux (DEF_type (TD_aux (TD_abbrev (_, _, A_aux (A_typ _, _)), _) as definition), _) ->
      let names = StringSet.of_list (emitted_type_names ctx definition) in
      let _, references = with_referenced_type_names ctx (fun () -> type_definition ctx definition) in
      Some { names; references = StringSet.diff references names }
  | _ -> None

let delayed_alias_names ctx definitions =
  let local_names = StringSet.of_list (emitted_type_import_names ctx definitions) in
  let aliases = List.filter_map (alias_dependencies ctx) definitions in
  let rec close delayed =
    let next =
      List.fold_left
        (fun delayed alias ->
          if
            (not (StringSet.is_empty (StringSet.diff alias.references local_names)))
            || not (StringSet.is_empty (StringSet.inter alias.references delayed))
          then StringSet.union delayed alias.names
          else delayed
        )
        delayed aliases
    in
    if StringSet.equal delayed next then delayed else close next
  in
  close StringSet.empty

let definition_emits_delayed_alias ctx delayed = function
  | DEF_aux (DEF_type definition, _) ->
      not (StringSet.is_empty (StringSet.inter delayed (StringSet.of_list (emitted_type_names ctx definition))))
  | _ -> false

let source_definition_lines ~preserve_structure ctx = function
  | DEF_aux (DEF_type definition, _) -> type_definition ctx definition
  | DEF_aux ((DEF_fundef _ | DEF_internal_mutrec _), _) as definition ->
      function_definition ~preserve_structure ctx definition
  | _ -> []

type source_module_render = {
  rendered_definitions : string list;
  delayed_definitions : string list;
  state_definitions : string list;
  reset_definitions : string list;
  referenced_values : IdSet.t;
  referenced_modules : StringSet.t;
  referenced_type_names : StringSet.t;
}

(* Type, constructor, and validity names are unique across the whole model and
   are imported unrenamed, so any of them can be visible in any module. *)
let program_type_level_names ctx =
  let add _ name names = StringSet.add name names in
  runtime_names |> Bindings.fold add ctx.type_names |> Bindings.fold add ctx.constructor_names
  |> Bindings.fold add ctx.record_validity_names

(* Values a module actually binds at its top level. [bound_value_names] is not
   usable here: it deliberately also collects function-local binders, so every
   local would collide with itself. *)
let module_value_names ctx definitions =
  let register_ids =
    List.filter_map
      (function DEF_aux (DEF_register (DEC_aux (DEC_reg (_, id, _), _)), _) -> Some id | _ -> None)
      definitions
  in
  List.fold_left
    (fun names id -> StringSet.add (value_name ctx id) names)
    StringSet.empty
    (emitted_value_ids ctx definitions @ register_ids)

let source_module_level_names ctx components definitions =
  let names = StringSet.union (program_type_level_names ctx) (module_value_names ctx definitions) in
  let names =
    match StringMap.find_opt (module_key components) ctx.value_import_names with
    | Some bindings -> Bindings.fold (fun _ name names -> StringSet.add name names) bindings names
    | None -> names
  in
  match StringMap.find_opt (module_key components) ctx.module_import_names with
  | Some aliases -> StringMap.fold (fun _ name names -> StringSet.add name names) aliases names
  | None -> names

let render_source_module ~preserve_structure ctx components definitions =
  let previous_module_names = !current_module_names in
  current_module_names := source_module_level_names ctx components definitions;
  Fun.protect ~finally:(fun () -> current_module_names := previous_module_names) @@ fun () ->
  let module_ctx = { ctx with current_module = Some components } in
  let delayed_aliases = delayed_alias_names module_ctx definitions in
  let rendered, late_values, late_modules =
    with_referenced_values module_ctx (fun () ->
        with_referenced_type_names module_ctx (fun () ->
            let regular_definitions =
              concat_map
                (fun definition ->
                  if definition_emits_delayed_alias module_ctx delayed_aliases definition then []
                  else source_definition_lines ~preserve_structure module_ctx definition
                )
                definitions
            in
            let delayed_definitions =
              concat_map
                (fun definition ->
                  if definition_emits_delayed_alias module_ctx delayed_aliases definition then
                    source_definition_lines ~preserve_structure module_ctx definition
                  else []
                )
                definitions
            in
            let reset_definitions = source_reset_function module_ctx definitions in
            (regular_definitions, delayed_definitions, reset_definitions)
        )
    )
  in
  let (rendered_definitions, delayed_definitions, reset_definitions), late_type_names = rendered in
  let state_rendered, state_values, state_modules =
    with_referenced_values module_ctx (fun () ->
        with_referenced_type_names module_ctx (fun () -> concat_map (source_state_definition module_ctx) definitions)
    )
  in
  let state_definitions, state_type_names = state_rendered in
  {
    rendered_definitions;
    delayed_definitions;
    state_definitions;
    reset_definitions;
    referenced_values = IdSet.union late_values state_values;
    referenced_modules = StringSet.union late_modules state_modules;
    referenced_type_names = StringSet.union late_type_names state_type_names;
  }

let source_reference_targets ctx modules current_components rendered =
  List.fold_left
    (fun targets (_, target_components, definitions) ->
      if same_module current_components target_components then targets
      else (
        let type_dependency =
          emitted_type_import_names ctx definitions
          |> List.exists (fun name -> StringSet.mem name rendered.referenced_type_names)
        in
        let value_dependency =
          emitted_value_ids ctx definitions |> List.exists (fun id -> IdSet.mem id rendered.referenced_values)
        in
        let module_dependency = StringSet.mem (module_key target_components) rendered.referenced_modules in
        if type_dependency || value_dependency || module_dependency then
          StringSet.add (module_key target_components) targets
        else targets
      )
    )
    StringSet.empty modules

let source_dependency_graph ctx modules rendered_modules =
  List.fold_left2
    (fun graph (_, components, _) rendered ->
      StringMap.add (module_key components) (source_reference_targets ctx modules components rendered) graph
    )
    StringMap.empty modules rendered_modules

let source_symbol_dependency_graph ctx modules rendered_modules =
  List.fold_left2
    (fun graph (_, current_components, _) rendered ->
      let dependencies =
        List.fold_left
          (fun dependencies (_, target_components, definitions) ->
            if same_module current_components target_components then dependencies
            else (
              let type_dependency =
                emitted_type_import_names ctx definitions
                |> List.exists (fun name -> StringSet.mem name rendered.referenced_type_names)
              in
              let value_dependency =
                emitted_value_ids ctx definitions |> List.exists (fun id -> IdSet.mem id rendered.referenced_values)
              in
              if type_dependency || value_dependency then StringSet.add (module_key target_components) dependencies
              else dependencies
            )
          )
          StringSet.empty modules
      in
      StringMap.add (module_key current_components) dependencies graph
    )
    StringMap.empty modules rendered_modules

let graph_reachable graph source target =
  let rec visit seen node =
    if String.equal node target then true
    else if StringSet.mem node seen then false
    else (
      let seen = StringSet.add node seen in
      match StringMap.find_opt node graph with
      | None -> false
      | Some dependencies -> StringSet.exists (visit seen) dependencies
    )
  in
  visit StringSet.empty source

let cyclic_type_module_edges ctx modules rendered_modules =
  let graph = source_dependency_graph ctx modules rendered_modules in
  List.fold_left2
    (fun qualified (_, components, _) rendered ->
      List.fold_left
        (fun qualified (_, target_components, definitions) ->
          let references_target =
            emitted_type_import_names ctx definitions
            |> List.exists (fun name -> StringSet.mem name rendered.referenced_type_names)
          in
          if
            references_target
            && (not (same_module components target_components))
            && graph_reachable graph (module_key target_components) (module_key components)
          then StringSet.add (module_edge_key components target_components) qualified
          else qualified
        )
        qualified modules
    )
    StringSet.empty modules rendered_modules

let cyclic_value_module_edges ctx modules rendered_modules =
  let graph = source_dependency_graph ctx modules rendered_modules in
  List.fold_left2
    (fun qualified (_, components, _) rendered ->
      IdSet.fold
        (fun id qualified ->
          match Bindings.find_opt id ctx.value_modules with
          | Some target_components
            when (not (same_module components target_components))
                 && graph_reachable graph (module_key target_components) (module_key components) ->
              StringSet.add (module_edge_key components target_components) qualified
          | _ -> qualified
        )
        rendered.referenced_values qualified
    )
    StringSet.empty modules rendered_modules

let order_package_modules ctx modules rendered_modules =
  let graph = source_symbol_dependency_graph ctx modules rendered_modules in
  let rec order ordered remaining =
    match remaining with
    | [] -> List.rev ordered
    | _ ->
        let has_incoming key =
          List.exists
            (fun (_, components, _) ->
              let source = module_key components in
              (not (String.equal source key))
              &&
              match StringMap.find_opt source graph with
              | Some dependencies -> StringSet.mem key dependencies
              | None -> false
            )
            remaining
        in
        let roots, rest =
          List.partition (fun (_, components, _) -> not (has_incoming (module_key components))) remaining
        in
        if roots = [] then List.rev_append ordered remaining else order (List.rev_append roots ordered) rest
  in
  order [] modules

let source_module_file ~package_name ~preserve_structure ctx modules source_label components definitions =
  let relative_import = String.make (List.length components) '.' in
  let module_ctx = { ctx with current_module = Some components } in
  let rendered = render_source_module ~preserve_structure ctx components definitions in
  let dependency_imports =
    source_module_dependency_imports package_name ctx modules components rendered.referenced_type_names
      rendered.referenced_values
    @ source_register_module_imports package_name ctx modules components rendered.referenced_modules
  in
  let all_definitions =
    rendered.rendered_definitions @ rendered.delayed_definitions @ rendered.state_definitions
    @ rendered.reset_definitions
  in
  let runtime_imports =
    explicit_import (relative_import ^ "_runtime")
      (imports_used_by all_definitions (context_runtime_import_names module_ctx))
  in
  let extern_import =
    match ctx.extern_module with Some module_name -> extern_imports_for module_name ctx all_definitions | _ -> []
  in
  {
    relative_path = module_file components;
    contents =
      String.concat "\n"
        ([generated_banner; "# Sail source: " ^ source_label; "from __future__ import annotations"; ""]
        @ runtime_imports @ python_imports_for all_definitions @ extern_import @ dependency_imports @ [""]
        @ all_definitions
        );
  }

let type_aggregation_imports ctx modules =
  concat_map
    (fun (_, components, definitions) ->
      match emitted_type_import_names ctx definitions with
      | [] -> []
      | names -> explicit_import ~reexport:true ("." ^ dotted_module components) names @ [""]
    )
    modules

let package_module_import alias components =
  match List.rev components with
  | leaf :: reversed_parents ->
      let parents = List.rev reversed_parents in
      let parent = match parents with [] -> "." | _ -> "." ^ dotted_module parents in
      ("from " ^ parent ^ " import " ^ leaf ^ " as " ^ alias, alias)
  | [] -> backend_error "empty Python package module path"

let package_value_imports ctx modules =
  concat_map
    (fun (_, components, definitions) ->
      match emitted_value_ids ctx definitions with
      | [] -> []
      | ids -> explicit_import ~reexport:true ("." ^ dotted_module components) (List.map (value_name ctx) ids) @ [""]
    )
    modules

let package_register_modules ctx modules =
  let used = ref StringSet.empty in
  List.mapi
    (fun index (_, components, definitions) ->
      let registers =
        List.filter_map
          (fun (DEF_aux (definition, _)) ->
            match definition with DEF_register (DEC_aux (DEC_reg (_, id, _), _)) -> Some id | _ -> None
          )
          definitions
      in
      match registers with
      | [] -> None
      | registers ->
          let preferred = "_register_" ^ String.concat "_" components in
          let alias = choose_name used preferred (preferred ^ "_" ^ string_of_int index) in
          let import, alias = package_module_import alias components in
          Some (import, alias, registers)
    )
    modules
  |> List.filter_map Fun.id

let package_metadata_names =
  [
    "__sail_types__";
    "__sail_functions__";
    "__sail_signatures__";
    "__sail_source_signatures__";
    "__sail_effects__";
    "__sail_externs__";
  ]

let package_init_file ctx effect_info ast modules type_import_names =
  let register_modules = package_register_modules ctx modules in
  let register_imports = List.map (fun (import, _, _) -> import) register_modules in
  let register_entries =
    concat_map
      (fun (_, alias, registers) -> List.map (fun id -> py_string (value_name ctx id) ^ ": " ^ alias) registers)
      register_modules
  in
  let register_module_names = List.map (fun (_, alias, _) -> alias) register_modules in
  let register_names = concat_map (fun (_, _, registers) -> List.map (value_name ctx) registers) register_modules in
  let metadata_lines = metadata ctx effect_info ast.defs in
  let extern_import, extern_reset, extern_finish =
    match ctx.extern_module with
    | Some module_name ->
        ( ["from " ^ module_name ^ " import ("; "    finish as _host_finish,"; "    reset as _host_reset,"; ")"; ""],
          ["    _host_reset()"],
          ["    _host_finish()"]
        )
    | None -> ([], [], ["    return None"])
  in
  let public_names =
    let declarations =
      context_runtime_import_names ctx @ type_import_names
      @ concat_map (fun (_, _, definitions) -> List.map (value_name ctx) (emitted_value_ids ctx definitions)) modules
      @ register_names @ ["reset"; "finish"]
      |> List.filter (fun name -> String.length name = 0 || not (Char.equal name.[0] '_'))
    in
    declarations @ package_metadata_names |> List.sort_uniq String.compare
  in
  let register_owner_lines =
    match register_entries with
    | [] -> ["_REGISTER_OWNERS = {}"; "_REGISTER_MODULES = ()"]
    | entries ->
        ["_REGISTER_OWNERS = {"]
        @ List.map (fun entry -> "    " ^ entry ^ ",") entries
        @ [
            "}";
            "_REGISTER_MODULES = ("
            ^ String.concat ", " register_module_names
            ^ (if List.length register_module_names = 1 then "," else "")
            ^ ")";
          ]
  in
  {
    relative_path = "__init__.py";
    contents =
      String.concat "\n"
        ([generated_banner; "from __future__ import annotations"; ""]
        @ explicit_import ~reexport:true "._runtime" (context_runtime_import_names ctx)
        @ package_value_imports ctx modules
        @ explicit_import ~reexport:true "._types" type_import_names
        @ register_imports @ extern_import @ [""] @ metadata_lines @ [""] @ register_owner_lines
        @ [""; "def reset() -> None:"; "    for _module in _REGISTER_MODULES:"; "        _module._reset_registers()"]
        @ extern_reset @ [""; "def finish() -> None:"] @ extern_finish
        @ [
            "";
            "def __getattr__(name: str):";
            "    try:";
            "        owner = _REGISTER_OWNERS[name]";
            "    except KeyError as error:";
            "        raise AttributeError(f\"module {__name__!r} has no attribute {name!r}\") from error";
            "    return getattr(owner, name)";
            "";
            "def __dir__() -> list[str]:";
            "    return sorted(set(globals()) | set(__all__))";
            "";
            "__all__ = [" ^ String.concat ", " (List.map py_string public_names) ^ "]";
            "";
          ]
        );
  }

let package_directory_init components =
  {
    relative_path = String.concat Filename.dir_sep components ^ Filename.dir_sep ^ "__init__.py";
    contents = generated_banner ^ "\n";
  }

let package_directory_inits modules =
  let rec prefixes = function
    | [] | [_] -> []
    | components ->
        let parent = Util.butlast components in
        parent :: prefixes parent
  in
  let _, directories =
    List.fold_left
      (fun (seen, files) (_, components, _) ->
        List.fold_left
          (fun (seen, files) directory ->
            let key = module_key directory in
            if StringSet.mem key seen then (seen, files)
            else (StringSet.add key seen, package_directory_init directory :: files)
          )
          (seen, files) (prefixes components)
      )
      (StringSet.empty, []) modules
  in
  List.rev directories

let generate_package ?runtime_module ?extern_module ?source_root ?(preserve_structure = false)
    ?(source_val_specs = Bindings.empty) ?(pydantic = false) ?(ethereum_fixed_bytes = []) ~package_name env effect_info
    ast =
  let enum_conversions = generated_enum_conversions ast.defs in
  let ast = without_generated_undefined_definitions ast in
  let ast = without_function_definitions enum_conversions.function_ids ast in
  let groups = source_definition_groups ast.defs in
  let modules = unique_module_components source_root groups in
  let type_modules = type_module_bindings modules in
  let value_modules = value_module_bindings modules in
  let register_modules = register_module_bindings modules in
  let ctx =
    make_context ~qualify_globals:true ~value_modules ~register_modules ~source_val_specs ~pydantic
      ~ethereum_fixed_bytes ~enum_conversions ?extern_module env ast
  in
  let ctx = { ctx with type_modules } in
  let type_import_names = emitted_type_import_names ctx ast.defs in
  let value_import_names = value_import_name_bindings ctx type_import_names modules in
  let module_import_names = module_import_name_bindings ctx type_import_names value_import_names modules in
  let ctx = { ctx with value_import_names; module_import_names } in
  let preliminary_renders =
    List.map (fun (_, components, defs) -> render_source_module ~preserve_structure ctx components defs) modules
  in
  let qualified_type_modules = cyclic_type_module_edges ctx modules preliminary_renders in
  let qualified_value_modules = cyclic_value_module_edges ctx modules preliminary_renders in
  let ordering_ctx = { ctx with qualified_value_modules } in
  let ordering_renders =
    List.map
      (fun (_, components, defs) -> render_source_module ~preserve_structure ordering_ctx components defs)
      modules
  in
  let ctx = { ctx with qualified_type_modules; qualified_value_modules } in
  let package_modules = order_package_modules ordering_ctx modules ordering_renders in
  let runtime_file =
    {
      relative_path = "_runtime.py";
      contents =
        ( match runtime_module with
        | None -> generated_banner ^ "\n" ^ runtime_source ctx runtime_module
        | Some _ ->
            String.concat "\n"
              [generated_banner; "from __future__ import annotations"; ""; runtime_source ctx runtime_module; ""]
        );
    }
  in
  let types_file =
    {
      relative_path = "_types.py";
      contents =
        String.concat "\n"
          ([generated_banner; "from __future__ import annotations"; ""] @ type_aggregation_imports ctx modules);
    }
  in
  let source_files =
    List.map
      (fun (source, components, defs) ->
        source_module_file ~package_name ~preserve_structure ctx modules
          (source_relative_path source_root source)
          components defs
      )
      modules
  in
  package_init_file ctx effect_info ast package_modules type_import_names
  :: runtime_file :: types_file :: package_directory_inits modules
  @ source_files

let generate ?runtime_module ?extern_module ?(preserve_structure = false) ?(source_val_specs = Bindings.empty)
    ?(pydantic = false) ?(ethereum_fixed_bytes = []) env effect_info ast =
  let enum_conversions = generated_enum_conversions ast.defs in
  let ast = without_generated_undefined_definitions ast in
  let ast = without_function_definitions enum_conversions.function_ids ast in
  let ctx = make_context ~source_val_specs ~pydantic ~ethereum_fixed_bytes ~enum_conversions ?extern_module env ast in
  (* Single-file output: the whole program shares one module scope. *)
  current_module_names := StringSet.union (program_type_level_names ctx) (module_value_names ctx ast.defs);
  let runtime = runtime_source ctx runtime_module in
  let type_lines =
    concat_map (function DEF_aux (DEF_type definition, _) -> type_definition ctx definition | _ -> []) ast.defs
  in
  let function_lines = concat_map (function_definition ~preserve_structure:false ctx) ast.defs in
  let definitions =
    if preserve_structure then concat_map (source_order_definition ctx) ast.defs
    else type_lines @ register_declarations ctx ast.defs @ function_lines @ top_level_let_definitions ctx ast.defs
  in
  let generated_body = definitions @ reset_function ctx ast.defs @ metadata ctx effect_info ast.defs @ ["reset()"] in
  let extern_import =
    match extern_module with Some module_name -> extern_imports_for module_name ctx generated_body | _ -> []
  in
  let generated =
    ( match runtime_module with
      | None -> [generated_banner; runtime]
      | Some _ -> [generated_banner; "from __future__ import annotations"; ""; runtime]
      )
    @ python_imports_for generated_body @ extern_import @ [""] @ generated_body
  in
  String.concat "\n" generated
