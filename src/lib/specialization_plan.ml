(****************************************************************************)
(* Backend-neutral representation-specialization provenance.               *)
(****************************************************************************)

open Ast
open Ast_util
open Jib
open Jib_util

type input = { path : string; digest : string }

type representation_choice = {
  position : string;
  semantic_type : string;
  represented_type : string;
  inferred_bound : string option;
  conversion : string;
}

type conversion = { conversion_id : string; source_type : string; destination_type : string; reason : string }

type call_edge = {
  call_id : string;
  callee_identity : string;
  source_name : string;
  type_arguments : string list;
  result_type : string;
  is_extern : bool;
}

type obligation_kind =
  | Representation_adequacy
  | Operation_refinement
  | Conversion_correctness
  | Call_compatibility
  | Path_condition_soundness
  | Exception_equivalence
  | Extern_refinement
  | Ownership_lifetime

type obligation_status = Reconstructible | Requires_proof | Unresolved | Not_applicable

type obligation = {
  obligation_id : string;
  kind : obligation_kind;
  subject : string;
  status : obligation_status;
  evidence : string;
}

type base_clone = {
  trace : Jib_compile.representation_specialization;
  source_identity : string;
  clone_identity : string;
  input : input;
  location : string;
}

type clone = {
  base : base_clone;
  representation_choices : representation_choice list;
  conversions : conversion list;
  calls : call_edge list;
  obligations : obligation list;
}

type t = {
  compiler_name : string;
  compiler_version : string;
  compiler_revision : string option;
  configuration_identity : string;
  inputs : input list;
  clones : clone list;
  json : Yojson.Safe.t;
}

let digest_string kind value = kind ^ ":md5:" ^ Digest.to_hex (Digest.string value)

let digest_file path =
  try Digest.to_hex (Digest.file path) with Sys_error _ -> Digest.to_hex (Digest.string ("missing:" ^ path))

let normalize_path path =
  let cwd = Sys.getcwd () in
  let prefix = cwd ^ Filename.dir_sep in
  if String.starts_with ~prefix path then
    String.sub path (String.length prefix) (String.length path - String.length prefix)
  else path

let input_of_location location =
  let path = Option.value ~default:"<unknown>" (Reporting.loc_file location) in
  { path = normalize_path path; digest = "md5:" ^ digest_file path }

let string_of_bound = function
  | None -> None
  | Some (lower, upper) -> Some (Big_int.to_string lower ^ ".." ^ Big_int.to_string upper)

let json_option f = function None -> `Null | Some value -> f value
let json_string_option = json_option (fun value -> `String value)
let json_strings values = `List (List.map (fun value -> `String value) values)

let string_of_obligation_kind = function
  | Representation_adequacy -> "representation_adequacy"
  | Operation_refinement -> "operation_refinement"
  | Conversion_correctness -> "conversion_correctness"
  | Call_compatibility -> "call_compatibility"
  | Path_condition_soundness -> "path_condition_soundness"
  | Exception_equivalence -> "exception_equivalence"
  | Extern_refinement -> "extern_refinement"
  | Ownership_lifetime -> "ownership_lifetime"

let string_of_obligation_status = function
  | Reconstructible -> "reconstructible"
  | Requires_proof -> "requires_proof"
  | Unresolved -> "unresolved"
  | Not_applicable -> "not_applicable"

let signature parameters result =
  "(" ^ String.concat "," (List.map string_of_ctyp parameters) ^ ")->" ^ string_of_ctyp result

let stable_span location =
  match Reporting.simp_loc location with
  | Some (start_position, end_position) ->
      Printf.sprintf "%d.%d-%d.%d" start_position.pos_lnum
        (start_position.pos_cnum - start_position.pos_bol)
        end_position.pos_lnum
        (end_position.pos_cnum - end_position.pos_bol)
  | None -> "unknown"

let source_identity trace input =
  digest_string "source"
    (String.concat "\x1f"
       [
         string_of_id trace.Jib_compile.source_id;
         signature trace.semantic_parameters trace.semantic_result;
         input.digest;
         stable_span trace.source_location;
       ]
    )

let clone_identity trace source_identity =
  let bounds =
    List.map string_of_bound trace.Jib_compile.argument_bounds @ [string_of_bound trace.result_bound]
    |> List.map (Option.value ~default:"unbounded")
    |> String.concat ","
  in
  digest_string "clone"
    (String.concat "\x1f" [source_identity; signature trace.represented_parameters trace.represented_result; bounds])

let compare_input left right =
  match String.compare left.digest right.digest with 0 -> String.compare left.path right.path | order -> order
let compare_base_clone left right = String.compare left.clone_identity right.clone_identity

let unique_sorted compare values =
  let values = List.sort compare values in
  let rec deduplicate acc = function
    | left :: (right :: _ as tail) when compare left right = 0 -> deduplicate acc tail
    | value :: tail -> deduplicate (value :: acc) tail
    | [] -> List.rev acc
  in
  deduplicate [] values

let make_choice position semantic represented bound =
  let semantic_type = string_of_ctyp semantic in
  let represented_type = string_of_ctyp represented in
  {
    position;
    semantic_type;
    represented_type;
    inferred_bound = string_of_bound bound;
    conversion = (if ctyp_equal semantic represented then "identity" else semantic_type ^ " -> " ^ represented_type);
  }

let make_obligation clone_identity kind subject status evidence =
  let kind_name = string_of_obligation_kind kind in
  {
    obligation_id = digest_string "obligation" (String.concat "\x1f" [clone_identity; kind_name; subject]);
    kind;
    subject;
    status;
    evidence;
  }

let choice_json choice =
  `Assoc
    [
      ("position", `String choice.position);
      ("semantic_type", `String choice.semantic_type);
      ("represented_type", `String choice.represented_type);
      ("inferred_bound", json_string_option choice.inferred_bound);
      ("conversion", `String choice.conversion);
    ]

let conversion_json conversion =
  `Assoc
    [
      ("id", `String conversion.conversion_id);
      ("source_type", `String conversion.source_type);
      ("destination_type", `String conversion.destination_type);
      ("reason", `String conversion.reason);
    ]

let call_json call =
  `Assoc
    [
      ("id", `String call.call_id);
      ("callee", `String call.callee_identity);
      ("source_name", `String call.source_name);
      ("type_arguments", json_strings call.type_arguments);
      ("result_type", `String call.result_type);
      ("extern", `Bool call.is_extern);
    ]

let obligation_json obligation =
  `Assoc
    [
      ("id", `String obligation.obligation_id);
      ("kind", `String (string_of_obligation_kind obligation.kind));
      ("subject", `String obligation.subject);
      ("status", `String (string_of_obligation_status obligation.status));
      ("evidence", `String obligation.evidence);
    ]

let create ~compiler_name ~compiler_version ~compiler_revision ~configuration ~input_locations traces =
  let configuration_identity =
    digest_string "configuration"
      ("specialization-plan-schema=1.0.0;representation-policy=c-specialize-v1;backend-symbols=excluded;"
     ^ configuration
      )
  in
  let base_clones =
    List.map
      (fun trace ->
        let input = input_of_location trace.Jib_compile.source_location in
        let location = Reporting.short_loc_to_string trace.source_location in
        let source_identity = source_identity trace input in
        let clone_identity = clone_identity trace source_identity in
        { trace; source_identity; clone_identity; input; location }
      )
      traces
    |> unique_sorted compare_base_clone
  in
  let inputs =
    List.filter_map
      (fun location ->
        match Reporting.loc_file location with None -> None | Some _ -> Some (input_of_location location)
      )
      input_locations
    @ List.map (fun clone -> clone.input) base_clones
    |> List.sort compare_input
    |> List.fold_left
         (fun inputs input ->
           match inputs with prior :: _ when String.equal prior.digest input.digest -> inputs | _ -> input :: inputs
         )
         []
    |> List.rev
  in
  let clone_ids =
    List.fold_left
      (fun bindings clone ->
        Ast_compare.Bindings.add clone.trace.Jib_compile.specialized_id clone.clone_identity bindings
      )
      Ast_compare.Bindings.empty base_clones
  in
  let enrich_clone base =
    let trace = base.trace in
    let representation_choices =
      List.mapi
        (fun index (semantic, represented, bound) ->
          make_choice ("argument:" ^ string_of_int index) semantic represented bound
        )
        (List.map2
           (fun (semantic, represented) bound -> (semantic, represented, bound))
           (List.combine trace.semantic_parameters trace.represented_parameters)
           trace.argument_bounds
        )
      @ [make_choice "result" trace.semantic_result trace.represented_result trace.result_bound]
    in
    let conversions =
      trace.conversions
      |> List.map (fun (source, destination) -> (string_of_ctyp source, string_of_ctyp destination))
      |> unique_sorted Stdlib.compare
      |> List.map (fun (source, destination) ->
          {
            conversion_id = digest_string "conversion" (String.concat "\x1f" [base.clone_identity; source; destination]);
            source_type = source;
            destination_type = destination;
            reason = "typed JIB assignment boundary";
          }
      )
      |> List.sort (fun left right -> String.compare left.conversion_id right.conversion_id)
    in
    let calls =
      trace.calls
      |> List.map (fun (callee, type_arguments, result, is_extern) ->
          let callee_identity =
            match Ast_compare.Bindings.find_opt callee clone_ids with
            | Some identity -> identity
            | None ->
                digest_string
                  (if is_extern then "extern" else "function")
                  (string_of_id callee ^ "\x1f" ^ signature type_arguments result)
          in
          ( callee_identity,
            string_of_id callee,
            List.map string_of_ctyp type_arguments,
            string_of_ctyp result,
            is_extern
          )
      )
      |> unique_sorted Stdlib.compare
      |> List.map (fun (callee_identity, source_name, type_arguments, result, is_extern) ->
          let subject =
            String.concat "\x1f"
              [
                base.clone_identity;
                callee_identity;
                source_name;
                String.concat "," type_arguments;
                result;
                string_of_bool is_extern;
              ]
          in
          {
            call_id = digest_string "call" subject;
            callee_identity;
            source_name;
            type_arguments;
            result_type = result;
            is_extern;
          }
      )
      |> List.sort (fun left right -> String.compare left.call_id right.call_id)
    in
    let has_extern = List.exists (fun call -> call.is_extern) calls in
    let has_argument_bounds =
      List.exists
        (fun choice -> (not (String.equal choice.position "result")) && Option.is_some choice.inferred_bound)
        representation_choices
    in
    let obligations =
      [
        make_obligation base.clone_identity Representation_adequacy "signature" Reconstructible
          "represented integer widths and inferred bounds";
        make_obligation base.clone_identity Operation_refinement "body" Requires_proof
          "specialized primitive operations refine mathematical Sail operations";
        make_obligation base.clone_identity Conversion_correctness "typed boundaries"
          (if conversions = [] then Not_applicable else Requires_proof)
          ( if conversions = [] then "clone has no typed conversion boundary"
            else "every recorded conversion preserves its source value"
          );
        make_obligation base.clone_identity Call_compatibility "call edges"
          (if calls = [] then Not_applicable else Reconstructible)
          ( if calls = [] then "clone has no call edge"
            else "caller arguments and callee representations are structurally compatible"
          );
        make_obligation base.clone_identity Path_condition_soundness "inferred bounds"
          (if has_argument_bounds then Requires_proof else Not_applicable)
          ( if has_argument_bounds then "bounds hold on every path reaching the clone"
            else "clone has no inferred argument bound"
          );
        make_obligation base.clone_identity Exception_equivalence "body" Requires_proof
          "specialization preserves Sail exception behavior";
        make_obligation base.clone_identity Extern_refinement "extern contracts"
          (if has_extern then Unresolved else Not_applicable)
          ( if has_extern then "external implementation contract requires independent evidence"
            else "clone has no extern call"
          );
        make_obligation base.clone_identity Ownership_lifetime "represented values" Requires_proof
          "storage and cleanup behavior is compatible with the represented types";
      ]
      |> List.sort (fun left right -> String.compare left.obligation_id right.obligation_id)
    in
    { base; representation_choices; conversions; calls; obligations }
  in
  let clones = List.map enrich_clone base_clones in
  let clone_json clone =
    let base = clone.base in
    let trace = base.trace in
    let has_extern = List.exists (fun call -> call.is_extern) clone.calls in
    `Assoc
      [
        ("id", `String base.clone_identity);
        ("source", `String base.source_identity);
        ("source_name", `String (string_of_id trace.source_id));
        ("clone_name", `String (string_of_id trace.specialized_id));
        ("location", `Assoc [("input", `String base.input.digest); ("span", `String base.location)]);
        ( "semantic_signature",
          `Assoc
            [
              ("parameters", json_strings (List.map string_of_ctyp trace.semantic_parameters));
              ("result", `String (string_of_ctyp trace.semantic_result));
            ]
        );
        ( "represented_signature",
          `Assoc
            [
              ("parameters", json_strings (List.map string_of_ctyp trace.represented_parameters));
              ("result", `String (string_of_ctyp trace.represented_result));
            ]
        );
        ("clone_key", `String base.clone_identity);
        ("representation_choices", `List (List.map choice_json clone.representation_choices));
        ("conversions", `List (List.map conversion_json clone.conversions));
        ("call_edges", `List (List.map call_json clone.calls));
        ("extern_contracts", `List (if has_extern then [`String "independent refinement evidence required"] else []));
        ("recursive", `Bool trace.recursive);
        ("obligations", `List (List.map obligation_json clone.obligations));
      ]
  in
  let clone_jsons = List.map clone_json clones in
  let unresolved =
    clone_jsons
    |> List.concat_map (fun clone -> Yojson.Safe.Util.member "obligations" clone |> Yojson.Safe.Util.to_list)
    |> List.filter (fun obligation ->
        Yojson.Safe.Util.member "status" obligation |> Yojson.Safe.Util.to_string = "unresolved"
    )
    |> List.map (fun obligation -> Yojson.Safe.Util.member "id" obligation)
    |> List.sort (fun left right -> String.compare (Yojson.Safe.Util.to_string left) (Yojson.Safe.Util.to_string right))
  in
  let json =
    `Assoc
      [
        ("schema", `String "https://sail-lang.org/schemas/specialization-plan/v1");
        ("schema_version", `String "1.0.0");
        ( "purpose",
          `String
            "Backend-neutral provenance for checking that representation-specialized JIB clones refine their Sail \
             definitions"
        );
        ( "trust_model",
          `Assoc
            [
              ("producer_trusted", `Bool false);
              ("checker_trusted", `Bool false);
              ("proof_consumer_reconstructs_obligations", `Bool true);
              ("backend_symbols_authoritative", `Bool false);
            ]
        );
        ("consumers", json_strings ["independent structural checker"; "Lean/Coq proof adapters"; "human review"]);
        ( "non_goals",
          json_strings
            [
              "certifying the compiler implementation";
              "stabilizing display names or C symbols";
              "proving extern implementations without supplied contracts";
            ]
        );
        ( "producer",
          `Assoc
            [
              ("name", `String compiler_name);
              ("version", `String compiler_version);
              ("revision", json_string_option compiler_revision);
            ]
        );
        ( "configuration",
          `Assoc
            [
              ("id", `String configuration_identity);
              ("representation_policy", `String "c-specialize-v1");
              ("backend_symbol_policy", `String "excluded-from-machine-plan");
            ]
        );
        ( "inputs",
          `List (List.map (fun input -> `Assoc [("id", `String input.digest); ("path", `String input.path)]) inputs)
        );
        ("clones", `List clone_jsons);
        ( "assumptions",
          `List
            ( if unresolved = [] then []
              else
                [
                  `Assoc
                    [
                      ("id", `String (digest_string "assumption" "extern-contracts"));
                      ("kind", `String "extern_contract");
                      ("text", `String "Extern implementations refine their declared Sail contracts.");
                    ];
                ]
            )
        );
        ("unresolved_obligations", `List unresolved);
        ("diagnostics", `List []);
        ( "canonicalization",
          `Assoc
            [
              ("encoding", `String "UTF-8 JSON");
              ("ordering", `String "lexicographic by stable id; object fields fixed by schema");
              ("identity_hash", `String "MD5 with domain-separated preimages");
            ]
        );
      ]
  in
  { compiler_name; compiler_version; compiler_revision; configuration_identity; inputs; clones; json }

let write_string path contents =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel contents)

let write_json path plan = write_string path (Yojson.Safe.pretty_to_string ~std:true plan.json ^ "\n")

let write_human ~backend_symbol path plan =
  let buffer = Buffer.create 4096 in
  let line format = Printf.ksprintf (fun value -> Buffer.add_string buffer (value ^ "\n")) format in
  line "# Sail Specialization Plan";
  line "";
  line "Schema: `1.0.0`  ";
  line "Producer: `%s %s`  " plan.compiler_name plan.compiler_version;
  line "Configuration identity: `%s`" plan.configuration_identity;
  line "";
  line "> Machine identities exclude backend symbols. The C symbols below are descriptive review aids only.";
  List.iter
    (fun clone ->
      let base = clone.base in
      let trace = base.trace in
      line "";
      line "## `%s`" base.clone_identity;
      line "";
      line "- Sail source name: `%s`" (string_of_id trace.source_id);
      line "- Generated clone name: `%s`" (string_of_id trace.specialized_id);
      line "- Emitted backend symbol: `%s`" (backend_symbol trace.specialized_id);
      line "- Source identity: `%s`" base.source_identity;
      line "- Source location: `%s`" base.location;
      line "- Semantic signature: `%s`" (signature trace.semantic_parameters trace.semantic_result);
      line "- Represented signature: `%s`" (signature trace.represented_parameters trace.represented_result);
      line "- Recursive clone: `%b`" trace.recursive
    )
    plan.clones;
  write_string path (Buffer.contents buffer)

let quoted contents = Printf.sprintf "%S" contents

let coq_quoted contents =
  let buffer = Buffer.create (String.length contents + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\"\""
      | '\n' | '\r' -> Buffer.add_char buffer ' '
      | character -> Buffer.add_char buffer character
      )
    contents;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let digest_suffix identity =
  match String.rindex_opt identity ':' with
  | Some index -> String.sub identity (index + 1) (String.length identity - index - 1)
  | None -> Digest.to_hex (Digest.string identity)

let obligation_name obligation = "obligation_" ^ digest_suffix obligation.obligation_id

let applicable obligation =
  match obligation.status with Not_applicable -> false | Reconstructible | Requires_proof | Unresolved -> true

let argument_choices clone =
  List.filter (fun choice -> not (String.equal choice.position "result")) clone.representation_choices

let result_choice clone = List.find (fun choice -> String.equal choice.position "result") clone.representation_choices

let inferred_argument_bounds clone =
  argument_choices clone
  |> List.filter_map (fun choice -> Option.map (fun bound -> (choice.position, bound)) choice.inferred_bound)

type proof_sort = Proof_value | Proof_values | Proof_outcome

type proof_binder = { binder_name : string; binder_sort : proof_sort }

type proof_term =
  | Variable of string
  | String_literal of string
  | String_list_literal of string list
  | Bound_list_literal of (string * string) list

type proof_relation =
  | Arguments_well_typed
  | Represented_values_valid
  | Value_well_typed
  | Represented_value_valid
  | Value_satisfies_bound
  | Arguments_represent
  | Represents
  | Sail_eval
  | Jib_eval
  | Conversion_eval
  | Call_arguments_represent
  | Sail_call
  | Jib_call
  | Extern_eval
  | Sail_reachable
  | Bounds_hold
  | Outcomes_refine
  | Exceptions_equivalent
  | Lifetime_compatible

type proposition =
  | Truth
  | Relation of proof_relation * proof_term list
  | Implication of proposition * proposition
  | Conjunction of proposition list
  | Universal of proof_binder list * proposition
  | Existential of proof_binder list * proposition

let variable name = Variable name
let string_literal value = String_literal value
let string_list_literal values = String_list_literal values
let relation name arguments = Relation (name, arguments)
let conjunction propositions = Conjunction propositions
let universally binders proposition = Universal (binders, proposition)
let existentially binders proposition = Existential (binders, proposition)
let implies premises conclusion = List.fold_right (fun premise body -> Implication (premise, body)) premises conclusion
let value name = { binder_name = name; binder_sort = Proof_value }
let values name = { binder_name = name; binder_sort = Proof_values }
let outcome name = { binder_name = name; binder_sort = Proof_outcome }

let obligation_proposition clone obligation =
  let base = clone.base in
  let trace = base.trace in
  let semantic_types = List.map string_of_ctyp trace.semantic_parameters in
  let represented_types = List.map string_of_ctyp trace.represented_parameters in
  let semantic_result = string_of_ctyp trace.semantic_result in
  let represented_result = string_of_ctyp trace.represented_result in
  let argument_bounds = inferred_argument_bounds clone in
  let result_bound = (result_choice clone).inferred_bound in
  let semantic_args = variable "semanticArgs" in
  let represented_args = variable "representedArgs" in
  let sail_outcome = variable "sailOutcome" in
  let jib_outcome = variable "jibOutcome" in
  let arguments_represent =
    relation Arguments_represent
      [string_list_literal semantic_types; string_list_literal represented_types; semantic_args; represented_args]
  in
  let sail_eval = relation Sail_eval [string_literal base.source_identity; semantic_args; sail_outcome] in
  let jib_eval = relation Jib_eval [string_literal base.clone_identity; represented_args; jib_outcome] in
  let outcomes_refine = relation Outcomes_refine [sail_outcome; jib_outcome] in
  let forward_eval extra_outcome_requirements =
    universally
      [values "semanticArgs"; values "representedArgs"; outcome "sailOutcome"]
      (implies [arguments_represent; sail_eval]
         (existentially [outcome "jibOutcome"] (conjunction (jib_eval :: outcomes_refine :: extra_outcome_requirements)))
      )
  in
  match obligation.kind with
  | Representation_adequacy ->
      let result_bound_requirements =
        match result_bound with
        | None -> []
        | Some bound -> [relation Value_satisfies_bound [string_literal bound; variable "semanticResult"]]
      in
      conjunction
        [
          universally
            [values "semanticArgs"]
            (implies
               [
                 relation Arguments_well_typed [string_list_literal semantic_types; semantic_args];
                 relation Bounds_hold [Bound_list_literal argument_bounds; semantic_args];
               ]
               (existentially
                  [values "representedArgs"]
                  (conjunction
                     [
                       arguments_represent;
                       relation Represented_values_valid [string_list_literal represented_types; represented_args];
                     ]
                  )
               )
            );
          universally
            [value "semanticResult"]
            (implies
               (relation Value_well_typed [string_literal semantic_result; variable "semanticResult"]
               :: result_bound_requirements
               )
               (existentially
                  [value "representedResult"]
                  (conjunction
                     [
                       relation Represents
                         [
                           string_literal semantic_result;
                           string_literal represented_result;
                           variable "semanticResult";
                           variable "representedResult";
                         ];
                       relation Represented_value_valid
                         [string_literal represented_result; variable "representedResult"];
                     ]
                  )
               )
            );
        ]
  | Operation_refinement -> forward_eval []
  | Conversion_correctness ->
      clone.conversions
      |> List.map (fun conversion ->
          universally
            [value "semanticValue"]
            (implies
               [relation Value_well_typed [string_literal conversion.source_type; variable "semanticValue"]]
               (existentially
                  [value "representedValue"]
                  (conjunction
                     [
                       relation Conversion_eval
                         [
                           string_literal conversion.conversion_id;
                           string_literal conversion.source_type;
                           string_literal conversion.destination_type;
                           variable "semanticValue";
                           variable "representedValue";
                         ];
                       relation Represents
                         [
                           string_literal conversion.source_type;
                           string_literal conversion.destination_type;
                           variable "semanticValue";
                           variable "representedValue";
                         ];
                       relation Represented_value_valid
                         [string_literal conversion.destination_type; variable "representedValue"];
                     ]
                  )
               )
            )
      )
      |> conjunction
  | Call_compatibility ->
      clone.calls
      |> List.map (fun call ->
          universally
            [values "semanticArgs"; values "representedArgs"; outcome "sailOutcome"]
            (implies
               [
                 relation Call_arguments_represent [string_literal call.call_id; semantic_args; represented_args];
                 relation Sail_call
                   [string_literal base.source_identity; string_literal call.call_id; semantic_args; sail_outcome];
               ]
               (existentially
                  [outcome "jibOutcome"]
                  (conjunction
                     [
                       relation Jib_call
                         [
                           string_literal base.clone_identity;
                           string_literal call.call_id;
                           string_literal call.callee_identity;
                           represented_args;
                           jib_outcome;
                         ];
                       outcomes_refine;
                     ]
                  )
               )
            )
      )
      |> conjunction
  | Path_condition_soundness ->
      universally
        [values "semanticArgs"]
        (implies
           [
             relation Arguments_well_typed [string_list_literal semantic_types; semantic_args];
             relation Sail_reachable [string_literal base.source_identity; semantic_args];
           ]
           (relation Bounds_hold [Bound_list_literal argument_bounds; semantic_args])
        )
  | Exception_equivalence -> forward_eval [relation Exceptions_equivalent [sail_outcome; jib_outcome]]
  | Extern_refinement ->
      clone.calls
      |> List.filter (fun call -> call.is_extern)
      |> List.map (fun call ->
          universally
            [values "semanticArgs"; values "representedArgs"; outcome "sailOutcome"]
            (implies
               [
                 relation Call_arguments_represent [string_literal call.call_id; semantic_args; represented_args];
                 relation Sail_call
                   [string_literal base.source_identity; string_literal call.call_id; semantic_args; sail_outcome];
               ]
               (existentially
                  [outcome "externOutcome"]
                  (conjunction
                     [
                       relation Extern_eval
                         [string_literal call.callee_identity; represented_args; variable "externOutcome"];
                       relation Outcomes_refine [sail_outcome; variable "externOutcome"];
                     ]
                  )
               )
            )
      )
      |> conjunction
  | Ownership_lifetime ->
      forward_eval [relation Lifetime_compatible [string_literal base.clone_identity; represented_args; jib_outcome]]

let lean_list render values = "[" ^ String.concat ", " (List.map render values) ^ "]"
let coq_list render values = "[" ^ String.concat "; " (List.map render values) ^ "]"

let lean_relation_name = function
  | Arguments_well_typed -> "argumentsWellTyped"
  | Represented_values_valid -> "representedValuesValid"
  | Value_well_typed -> "valueWellTyped"
  | Represented_value_valid -> "representedValueValid"
  | Value_satisfies_bound -> "valueSatisfiesBound"
  | Arguments_represent -> "argumentsRepresent"
  | Represents -> "represents"
  | Sail_eval -> "sailEval"
  | Jib_eval -> "jibEval"
  | Conversion_eval -> "conversionEval"
  | Call_arguments_represent -> "callArgumentsRepresent"
  | Sail_call -> "sailCall"
  | Jib_call -> "jibCall"
  | Extern_eval -> "externEval"
  | Sail_reachable -> "sailReachable"
  | Bounds_hold -> "boundsHold"
  | Outcomes_refine -> "outcomesRefine"
  | Exceptions_equivalent -> "exceptionsEquivalent"
  | Lifetime_compatible -> "lifetimeCompatible"

let coq_relation_name = function
  | Arguments_well_typed -> "sem_arguments_well_typed"
  | Represented_values_valid -> "sem_represented_values_valid"
  | Value_well_typed -> "sem_value_well_typed"
  | Represented_value_valid -> "sem_represented_value_valid"
  | Value_satisfies_bound -> "sem_value_satisfies_bound"
  | Arguments_represent -> "sem_arguments_represent"
  | Represents -> "sem_represents"
  | Sail_eval -> "sem_sail_eval"
  | Jib_eval -> "sem_jib_eval"
  | Conversion_eval -> "sem_conversion_eval"
  | Call_arguments_represent -> "sem_call_arguments_represent"
  | Sail_call -> "sem_sail_call"
  | Jib_call -> "sem_jib_call"
  | Extern_eval -> "sem_extern_eval"
  | Sail_reachable -> "sem_sail_reachable"
  | Bounds_hold -> "sem_bounds_hold"
  | Outcomes_refine -> "sem_outcomes_refine"
  | Exceptions_equivalent -> "sem_exceptions_equivalent"
  | Lifetime_compatible -> "sem_lifetime_compatible"

let lean_sort = function Proof_value -> "S.Value" | Proof_values -> "List S.Value" | Proof_outcome -> "S.Outcome"

let coq_sort = function
  | Proof_value -> "sem_value S"
  | Proof_values -> "list (sem_value S)"
  | Proof_outcome -> "sem_outcome S"

let render_lean_term = function
  | Variable name -> name
  | String_literal value -> quoted value
  | String_list_literal values -> lean_list quoted values
  | Bound_list_literal bounds ->
      lean_list (fun (position, bound) -> "(" ^ quoted position ^ ", " ^ quoted bound ^ ")") bounds

let render_coq_term = function
  | Variable name -> name
  | String_literal value -> coq_quoted value
  | String_list_literal values -> coq_list coq_quoted values
  | Bound_list_literal bounds ->
      coq_list (fun (position, bound) -> "(" ^ coq_quoted position ^ ", " ^ coq_quoted bound ^ ")") bounds

let rec render_lean_proposition = function
  | Truth -> "True"
  | Relation (name, arguments) ->
      "S." ^ lean_relation_name name ^ " " ^ String.concat " " (List.map render_lean_term arguments)
  | Implication (premise, conclusion) ->
      "(" ^ render_lean_proposition premise ^ " → " ^ render_lean_proposition conclusion ^ ")"
  | Conjunction [] -> "True"
  | Conjunction [proposition] -> render_lean_proposition proposition
  | Conjunction propositions -> "(" ^ String.concat " ∧ " (List.map render_lean_proposition propositions) ^ ")"
  | Universal (binders, proposition) ->
      let binders =
        binders
        |> List.map (fun binder -> "(" ^ binder.binder_name ^ " : " ^ lean_sort binder.binder_sort ^ ")")
        |> String.concat " "
      in
      "(∀ " ^ binders ^ ", " ^ render_lean_proposition proposition ^ ")"
  | Existential (binders, proposition) ->
      let binders =
        binders
        |> List.map (fun binder -> "(" ^ binder.binder_name ^ " : " ^ lean_sort binder.binder_sort ^ ")")
        |> String.concat " "
      in
      "(∃ " ^ binders ^ ", " ^ render_lean_proposition proposition ^ ")"

let rec render_coq_proposition = function
  | Truth -> "True"
  | Relation (name, arguments) -> coq_relation_name name ^ " S " ^ String.concat " " (List.map render_coq_term arguments)
  | Implication (premise, conclusion) ->
      "(" ^ render_coq_proposition premise ^ " -> " ^ render_coq_proposition conclusion ^ ")"
  | Conjunction [] -> "True"
  | Conjunction [proposition] -> render_coq_proposition proposition
  | Conjunction propositions -> "(" ^ String.concat " /\\ " (List.map render_coq_proposition propositions) ^ ")"
  | Universal (binders, proposition) ->
      let binders =
        binders
        |> List.map (fun binder -> "(" ^ binder.binder_name ^ " : " ^ coq_sort binder.binder_sort ^ ")")
        |> String.concat " "
      in
      "(forall " ^ binders ^ ", " ^ render_coq_proposition proposition ^ ")"
  | Existential (binders, proposition) ->
      let binders =
        binders
        |> List.map (fun binder -> "(" ^ binder.binder_name ^ " : " ^ coq_sort binder.binder_sort ^ ")")
        |> String.concat " "
      in
      "(exists " ^ binders ^ ", " ^ render_coq_proposition proposition ^ ")"

let iter_obligations plan callback =
  List.iter (fun clone -> List.iter (fun obligation -> callback clone obligation) clone.obligations) plan.clones

let write_lean path plan =
  let buffer = Buffer.create 16384 in
  let line format = Printf.ksprintf (fun value -> Buffer.add_string buffer (value ^ "\n")) format in
  line "-- Generated by Sail. Regenerate this definitions file; keep proofs in a separate file.";
  line "-- The compiler and this semantic interface are untrusted inputs to downstream proofs.";
  line "";
  line "namespace Sail.Specialization";
  line "";
  line "structure Semantics where";
  line "  Value : Type";
  line "  Outcome : Type";
  line "  argumentsWellTyped : List String → List Value → Prop";
  line "  representedValuesValid : List String → List Value → Prop";
  line "  valueWellTyped : String → Value → Prop";
  line "  representedValueValid : String → Value → Prop";
  line "  valueSatisfiesBound : String → Value → Prop";
  line "  argumentsRepresent : List String → List String → List Value → List Value → Prop";
  line "  represents : String → String → Value → Value → Prop";
  line "  sailEval : String → List Value → Outcome → Prop";
  line "  jibEval : String → List Value → Outcome → Prop";
  line "  conversionEval : String → String → String → Value → Value → Prop";
  line "  callArgumentsRepresent : String → List Value → List Value → Prop";
  line "  sailCall : String → String → List Value → Outcome → Prop";
  line "  jibCall : String → String → String → List Value → Outcome → Prop";
  line "  externEval : String → List Value → Outcome → Prop";
  line "  sailReachable : String → List Value → Prop";
  line "  boundsHold : List (String × String) → List Value → Prop";
  line "  outcomesRefine : Outcome → Outcome → Prop";
  line "  exceptionsEquivalent : Outcome → Outcome → Prop";
  line "  lifetimeCompatible : String → List Value → Outcome → Prop";
  line "";
  line "structure ObligationMetadata where";
  line "  id : String";
  line "  clone : String";
  line "  kind : String";
  line "  subject : String";
  line "  status : String";
  line "  evidence : String";
  line "";
  iter_obligations plan (fun clone obligation ->
      if applicable obligation then (
        line "def %s (S : Semantics) : Prop :=" (obligation_name obligation);
        line "  %s" (render_lean_proposition (obligation_proposition clone obligation));
        line ""
      )
  );
  line "def generatedObligations : List ObligationMetadata :=";
  line "  [";
  let metadata = ref [] in
  iter_obligations plan (fun clone obligation -> metadata := (clone, obligation) :: !metadata);
  List.rev !metadata
  |> List.iteri (fun index (clone, obligation) ->
      let suffix = if index + 1 = List.length !metadata then "" else "," in
      line "    { id := %s, clone := %s, kind := %s, subject := %s, status := %s, evidence := %s }%s"
        (quoted obligation.obligation_id) (quoted clone.base.clone_identity)
        (quoted (string_of_obligation_kind obligation.kind))
        (quoted obligation.subject)
        (quoted (string_of_obligation_status obligation.status))
        (quoted obligation.evidence) suffix
  );
  line "  ]";
  line "";
  line "structure Complete (S : Semantics) : Prop where";
  let applicable_obligations = ref [] in
  iter_obligations plan (fun _ obligation ->
      if applicable obligation then applicable_obligations := obligation :: !applicable_obligations
  );
  ( match List.rev !applicable_obligations with
  | [] -> line "  noObligations : True"
  | obligations ->
      List.iter
        (fun obligation ->
          line "  proof_%s : %s S" (digest_suffix obligation.obligation_id) (obligation_name obligation)
        )
        obligations
  );
  line "";
  line "end Sail.Specialization";
  write_string path (Buffer.contents buffer)

let write_coq path plan =
  let buffer = Buffer.create 16384 in
  let line format = Printf.ksprintf (fun value -> Buffer.add_string buffer (value ^ "\n")) format in
  line "(* Generated by Sail. Regenerate this definitions file; keep proofs in a separate file. *)";
  line "(* The compiler and this semantic interface are untrusted inputs to downstream proofs. *)";
  line "";
  line "From Stdlib Require Import String List.";
  line "Import ListNotations.";
  line "Open Scope string_scope.";
  line "";
  line "Module SailSpecialization.";
  line "";
  line "Record Semantics : Type := {";
  line "  sem_value : Type;";
  line "  sem_outcome : Type;";
  line "  sem_arguments_well_typed : list string -> list sem_value -> Prop;";
  line "  sem_represented_values_valid : list string -> list sem_value -> Prop;";
  line "  sem_value_well_typed : string -> sem_value -> Prop;";
  line "  sem_represented_value_valid : string -> sem_value -> Prop;";
  line "  sem_value_satisfies_bound : string -> sem_value -> Prop;";
  line "  sem_arguments_represent : list string -> list string -> list sem_value -> list sem_value -> Prop;";
  line "  sem_represents : string -> string -> sem_value -> sem_value -> Prop;";
  line "  sem_sail_eval : string -> list sem_value -> sem_outcome -> Prop;";
  line "  sem_jib_eval : string -> list sem_value -> sem_outcome -> Prop;";
  line "  sem_conversion_eval : string -> string -> string -> sem_value -> sem_value -> Prop;";
  line "  sem_call_arguments_represent : string -> list sem_value -> list sem_value -> Prop;";
  line "  sem_sail_call : string -> string -> list sem_value -> sem_outcome -> Prop;";
  line "  sem_jib_call : string -> string -> string -> list sem_value -> sem_outcome -> Prop;";
  line "  sem_extern_eval : string -> list sem_value -> sem_outcome -> Prop;";
  line "  sem_sail_reachable : string -> list sem_value -> Prop;";
  line "  sem_bounds_hold : list (string * string) -> list sem_value -> Prop;";
  line "  sem_outcomes_refine : sem_outcome -> sem_outcome -> Prop;";
  line "  sem_exceptions_equivalent : sem_outcome -> sem_outcome -> Prop;";
  line "  sem_lifetime_compatible : string -> list sem_value -> sem_outcome -> Prop";
  line "}.";
  line "";
  line "Record ObligationMetadata : Type := {";
  line "  obligation_metadata_id : string;";
  line "  obligation_metadata_clone : string;";
  line "  obligation_metadata_kind : string;";
  line "  obligation_metadata_subject : string;";
  line "  obligation_metadata_status : string;";
  line "  obligation_metadata_evidence : string";
  line "}.";
  line "";
  iter_obligations plan (fun clone obligation ->
      if applicable obligation then (
        line "Definition %s (S : Semantics) : Prop :=" (obligation_name obligation);
        line "  %s." (render_coq_proposition (obligation_proposition clone obligation));
        line ""
      )
  );
  line "Definition generated_obligations : list ObligationMetadata :=";
  line "  [";
  let metadata = ref [] in
  iter_obligations plan (fun clone obligation -> metadata := (clone, obligation) :: !metadata);
  List.rev !metadata
  |> List.iteri (fun index (clone, obligation) ->
      let suffix = if index + 1 = List.length !metadata then "" else ";" in
      line "    {| obligation_metadata_id := %s; obligation_metadata_clone := %s;" (coq_quoted obligation.obligation_id)
        (coq_quoted clone.base.clone_identity);
      line "       obligation_metadata_kind := %s; obligation_metadata_subject := %s;"
        (coq_quoted (string_of_obligation_kind obligation.kind))
        (coq_quoted obligation.subject);
      line "       obligation_metadata_status := %s; obligation_metadata_evidence := %s |}%s"
        (coq_quoted (string_of_obligation_status obligation.status))
        (coq_quoted obligation.evidence) suffix
  );
  line "  ].";
  line "";
  line "Record Complete (S : Semantics) : Prop := {";
  let applicable_obligations = ref [] in
  iter_obligations plan (fun _ obligation ->
      if applicable obligation then applicable_obligations := obligation :: !applicable_obligations
  );
  ( match List.rev !applicable_obligations with
  | [] -> line "  no_obligations : True"
  | obligations ->
      List.iteri
        (fun index obligation ->
          let suffix = if index + 1 = List.length obligations then "" else ";" in
          line "  proof_%s : %s S%s" (digest_suffix obligation.obligation_id) (obligation_name obligation) suffix
        )
        obligations
  );
  line "}.";
  line "";
  line "End SailSpecialization.";
  write_string path (Buffer.contents buffer)
