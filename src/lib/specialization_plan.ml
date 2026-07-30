(****************************************************************************)
(* Backend-neutral representation-specialization provenance.               *)
(****************************************************************************)

open Ast
open Ast_util
open Jib
open Jib_util

type input = { path : string; digest : string }

type clone = {
  trace : Jib_compile.representation_specialization;
  source_identity : string;
  clone_identity : string;
  input : input;
  location : string;
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
let compare_clone left right = String.compare left.clone_identity right.clone_identity

let json_id = function
  | `Assoc fields -> Yojson.Safe.Util.member "id" (`Assoc fields) |> Yojson.Safe.Util.to_string
  | _ -> ""

let sort_json_by_id = List.sort (fun left right -> String.compare (json_id left) (json_id right))

let unique_sorted compare values =
  let values = List.sort compare values in
  let rec deduplicate acc = function
    | left :: (right :: _ as tail) when compare left right = 0 -> deduplicate acc tail
    | value :: tail -> deduplicate (value :: acc) tail
    | [] -> List.rev acc
  in
  deduplicate [] values

let choice_json position semantic represented bound =
  `Assoc
    [
      ("position", `String position);
      ("semantic_type", `String (string_of_ctyp semantic));
      ("represented_type", `String (string_of_ctyp represented));
      ("inferred_bound", json_string_option (string_of_bound bound));
      ( "conversion",
        `String
          ( if ctyp_equal semantic represented then "identity"
            else string_of_ctyp semantic ^ " -> " ^ string_of_ctyp represented
          )
      );
    ]

let obligation clone_identity kind subject status evidence =
  let id = digest_string "obligation" (String.concat "\x1f" [clone_identity; kind; subject]) in
  `Assoc
    [
      ("id", `String id);
      ("kind", `String kind);
      ("subject", `String subject);
      ("status", `String status);
      ("evidence", `String evidence);
    ]

let create ~compiler_name ~compiler_version ~compiler_revision ~configuration ~input_locations traces =
  let configuration_identity =
    digest_string "configuration"
      ("specialization-plan-schema=1.0.0;representation-policy=c-specialize-v1;backend-symbols=excluded;"
     ^ configuration
      )
  in
  let clones =
    List.map
      (fun trace ->
        let input = input_of_location trace.Jib_compile.source_location in
        let location = Reporting.short_loc_to_string trace.source_location in
        let source_identity = source_identity trace input in
        let clone_identity = clone_identity trace source_identity in
        { trace; source_identity; clone_identity; input; location }
      )
      traces
    |> unique_sorted compare_clone
  in
  let inputs =
    List.filter_map
      (fun location ->
        match Reporting.loc_file location with None -> None | Some _ -> Some (input_of_location location)
      )
      input_locations
    @ List.map (fun clone -> clone.input) clones
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
      Ast_compare.Bindings.empty clones
  in
  let clone_json clone =
    let trace = clone.trace in
    let choices =
      List.mapi
        (fun index (semantic, represented, bound) ->
          choice_json ("argument:" ^ string_of_int index) semantic represented bound
        )
        (List.map2
           (fun (semantic, represented) bound -> (semantic, represented, bound))
           (List.combine trace.semantic_parameters trace.represented_parameters)
           trace.argument_bounds
        )
      @ [choice_json "result" trace.semantic_result trace.represented_result trace.result_bound]
    in
    let conversions =
      trace.conversions
      |> List.map (fun (source, destination) -> (string_of_ctyp source, string_of_ctyp destination))
      |> unique_sorted Stdlib.compare
      |> List.map (fun (source, destination) ->
          `Assoc
            [
              ( "id",
                `String (digest_string "conversion" (String.concat "\x1f" [clone.clone_identity; source; destination]))
              );
              ("source_type", `String source);
              ("destination_type", `String destination);
              ("reason", `String "typed JIB assignment boundary");
            ]
      )
      |> sort_json_by_id
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
                clone.clone_identity;
                callee_identity;
                source_name;
                String.concat "," type_arguments;
                result;
                string_of_bool is_extern;
              ]
          in
          `Assoc
            [
              ("id", `String (digest_string "call" subject));
              ("callee", `String callee_identity);
              ("source_name", `String source_name);
              ("type_arguments", json_strings type_arguments);
              ("result_type", `String result);
              ("extern", `Bool is_extern);
            ]
      )
      |> sort_json_by_id
    in
    let has_extern = List.exists (fun (_, _, _, is_extern) -> is_extern) trace.calls in
    let obligations =
      [
        obligation clone.clone_identity "representation_adequacy" "signature" "reconstructible"
          "represented integer widths and inferred bounds";
        obligation clone.clone_identity "operation_refinement" "body" "requires_proof"
          "specialized primitive operations refine mathematical Sail operations";
        obligation clone.clone_identity "conversion_correctness" "typed boundaries" "requires_proof"
          "every recorded conversion preserves its source value";
        obligation clone.clone_identity "call_compatibility" "call edges" "reconstructible"
          "caller arguments and callee representations are structurally compatible";
        obligation clone.clone_identity "path_condition_soundness" "inferred bounds" "requires_proof"
          "bounds hold on every path reaching the clone";
        obligation clone.clone_identity "exception_equivalence" "body" "requires_proof"
          "specialization preserves Sail exception behavior";
        obligation clone.clone_identity "extern_refinement" "extern contracts"
          (if has_extern then "unresolved" else "not_applicable")
          ( if has_extern then "external implementation contract requires independent evidence"
            else "clone has no extern call"
          );
        obligation clone.clone_identity "ownership_lifetime" "represented values" "requires_proof"
          "storage and cleanup behavior is compatible with the represented types";
      ]
      |> sort_json_by_id
    in
    `Assoc
      [
        ("id", `String clone.clone_identity);
        ("source", `String clone.source_identity);
        ("source_name", `String (string_of_id trace.source_id));
        ("clone_name", `String (string_of_id trace.specialized_id));
        ("location", `Assoc [("input", `String clone.input.digest); ("span", `String clone.location)]);
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
        ("clone_key", `String clone.clone_identity);
        ("representation_choices", `List choices);
        ("conversions", `List conversions);
        ("call_edges", `List calls);
        ("extern_contracts", `List (if has_extern then [`String "independent refinement evidence required"] else []));
        ("recursive", `Bool trace.recursive);
        ("obligations", `List obligations);
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
      let trace = clone.trace in
      line "";
      line "## `%s`" clone.clone_identity;
      line "";
      line "- Sail source name: `%s`" (string_of_id trace.source_id);
      line "- Generated clone name: `%s`" (string_of_id trace.specialized_id);
      line "- Emitted backend symbol: `%s`" (backend_symbol trace.specialized_id);
      line "- Source identity: `%s`" clone.source_identity;
      line "- Source location: `%s`" clone.location;
      line "- Semantic signature: `%s`" (signature trace.semantic_parameters trace.semantic_result);
      line "- Represented signature: `%s`" (signature trace.represented_parameters trace.represented_result);
      line "- Recursive clone: `%b`" trace.recursive
    )
    plan.clones;
  write_string path (Buffer.contents buffer)
