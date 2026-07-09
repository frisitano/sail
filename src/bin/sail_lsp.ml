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
(*  Copyright (c) 2013-2026                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Mark Wassell                                                          *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

(** A small stdio LSP server for Sail editor integration.

    This starts with source indexing and generated-C navigation because those are useful without changing the compiler
    pipeline. It deliberately speaks the JSON-RPC/LSP framing directly using Yojson, so the initial executable does not
    add an LSP dependency to the Sail package set. *)

module Json = Yojson.Safe
module Sail = Libsail

type position = { line : int; character : int }

type range = { start_pos : position; end_pos : position }

type symbol = { name : string; kind : int; detail : string; uri : string; range : range; selection_range : range }

type located_range = { loc_uri : string; loc_range : range }

type source_graph_entry = {
  graph_name : string;
  graph_kind : string;
  graph_uri : string;
  graph_range : range;
  graph_selection_range : range;
  graph_origin : string;
  graph_compiler_kind : string option;
  graph_type : string option;
  graph_type_source : string option;
  graph_doc_url : string option;
  graph_c_name : string option;
  graph_c_source : string option;
  graph_c_location : (string * range) option;
  graph_references : located_range list;
}

let jsonrpc = "2.0"

let text_documents : (string, string) Hashtbl.t = Hashtbl.create 16

let server_launch_cwd = Sys.getcwd ()

let root_path = ref None

let configured_c_output = ref None

let configured_c_map = ref None

let configured_docinfo = ref None

let configured_artifact_index = ref None

let configured_sail_executable = ref "sail"

let configured_project = ref None

let configured_modules = ref []

let configured_modules_explicit = ref false

let configured_all_modules = ref true

let configured_all_modules_explicit = ref false

let diagnostics_enabled = ref true

let shutdown_requested = ref false

type compiler_model = { compiler_ast : Sail.Type_check.typed_ast; compiler_env : Sail.Type_check.Env.t }

let compiler_model_cache : (string, compiler_model) Hashtbl.t = Hashtbl.create 4

let compiler_model_failure_cache : (string, unit) Hashtbl.t = Hashtbl.create 4

let source_graph_cache : (string, source_graph_entry list) Hashtbl.t = Hashtbl.create 4

let clear_compiler_env_cache () =
  Hashtbl.clear compiler_model_cache;
  Hashtbl.clear compiler_model_failure_cache;
  Hashtbl.clear source_graph_cache

let root_or_cwd () = match !root_path with Some root -> root | None -> Sys.getcwd ()

let c_output_arg =
  [
    ("--stdio", Arg.Unit (fun () -> ()), " Use standard input/output for LSP communication.");
    ( "--c-output",
      Arg.String (fun path -> configured_c_output := Some path),
      "FILE Generated C implementation file to use for Sail-to-C navigation."
    );
    ( "--c-map",
      Arg.String (fun path -> configured_c_map := Some path),
      "FILE JSON sidecar mapping Sail symbols to generated C/C++ symbols."
    );
    ( "--docinfo",
      Arg.String (fun path -> configured_docinfo := Some path),
      "FILE Sail documentation info JSON to use for hover/documentation."
    );
    ( "--artifact-index",
      Arg.String (fun path -> configured_artifact_index := Some path),
      "FILE Sail LSP artifact manifest, conventionally sail.lsp.json."
    );
    ( "--sail",
      Arg.String (fun path -> configured_sail_executable := path),
      "FILE Sail compiler executable for diagnostics."
    );
    ( "--project",
      Arg.String (fun path -> configured_project := Some path),
      "FILE Sail project file to use for compiler-backed diagnostics."
    );
    ( "--module",
      Arg.String
        (fun name ->
          configured_modules_explicit := true;
          configured_modules := !configured_modules @ [name]
        ),
      "NAME Sail project module to check. May be repeated."
    );
    ( "--all-modules",
      Arg.Unit
        (fun () ->
          configured_all_modules_explicit := true;
          configured_all_modules := true
        ),
      " Check all modules when using --project."
    );
    ( "--no-all-modules",
      Arg.Unit
        (fun () ->
          configured_all_modules_explicit := true;
          configured_all_modules := false
        ),
      " Do not check all modules when using --project and no --module arguments are provided."
    );
    ("--no-diagnostics", Arg.Clear diagnostics_enabled, " Disable compiler-backed diagnostics.");
  ]

let () =
  Arg.parse c_output_arg
    (fun arg -> Printf.eprintf "sail_lsp: ignoring positional argument %S\n%!" arg)
    "sail_lsp [--stdio] [--c-output FILE] [--c-map FILE] [--docinfo FILE] [--artifact-index FILE] [--sail FILE] \
     [--project FILE] [--module NAME] [--all-modules] [--no-all-modules] [--no-diagnostics]"

let drop_trailing_cr s =
  let len = String.length s in
  if len > 0 && s.[len - 1] = '\r' then String.sub s 0 (len - 1) else s

let starts_with ~prefix s =
  let len = String.length prefix in
  String.length s >= len && String.sub s 0 len = prefix

let ends_with ~suffix s =
  let len = String.length suffix in
  let start = String.length s - len in
  start >= 0 && String.sub s start len = suffix

let hex_value = function
  | '0' .. '9' as c -> Some (Char.code c - Char.code '0')
  | 'a' .. 'f' as c -> Some (10 + Char.code c - Char.code 'a')
  | 'A' .. 'F' as c -> Some (10 + Char.code c - Char.code 'A')
  | _ -> None

let percent_decode s =
  let len = String.length s in
  let buf = Buffer.create len in
  let rec loop i =
    if i >= len then Buffer.contents buf
    else (
      match s.[i] with
      | '%' when i + 2 < len -> (
          match (hex_value s.[i + 1], hex_value s.[i + 2]) with
          | Some hi, Some lo ->
              Buffer.add_char buf (Char.chr ((hi lsl 4) + lo));
              loop (i + 3)
          | _ ->
              Buffer.add_char buf s.[i];
              loop (i + 1)
        )
      | c ->
          Buffer.add_char buf c;
          loop (i + 1)
    )
  in
  loop 0

let percent_encode_path s =
  let buf = Buffer.create (String.length s) in
  String.iter
    (function
      | ('A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '/' | '.' | '-' | '_' | '~') as c -> Buffer.add_char buf c
      | c -> Buffer.add_string buf (Printf.sprintf "%%%02X" (Char.code c))
      )
    s;
  Buffer.contents buf

let path_of_uri uri =
  if starts_with ~prefix:"file://" uri then (
    let path = String.sub uri 7 (String.length uri - 7) in
    let path = if starts_with ~prefix:"localhost/" path then String.sub path 9 (String.length path - 9) else path in
    percent_decode path
  )
  else uri

let uri_of_path path =
  let path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path in
  let path = try Unix.realpath path with Unix.Unix_error _ | Sys_error _ -> path in
  "file://" ^ percent_encode_path path

let json_member key = function `Assoc fields -> List.assoc_opt key fields | _ -> None

let json_string_member key json = match json_member key json with Some (`String s) -> Some s | _ -> None

let json_int_member key json = match json_member key json with Some (`Int n) -> Some n | _ -> None

let json_bool_member key json = match json_member key json with Some (`Bool b) -> Some b | _ -> None

let json_list_member key json = match json_member key json with Some (`List xs) -> Some xs | _ -> None

let json_assoc_member key json = match json_member key json with Some (`Assoc fields) -> Some fields | _ -> None

let json_string_value = function `String s -> Some s | _ -> None

let json_assoc_value = function `Assoc fields -> Some fields | _ -> None

let json_string_list_member key json =
  match json_list_member key json with Some values -> Some (List.filter_map json_string_value values) | None -> None

module Source_location = struct
  let json_position position = `Assoc [("line", `Int position.line); ("character", `Int position.character)]

  let json_range range = `Assoc [("start", json_position range.start_pos); ("end", json_position range.end_pos)]

  let location_json uri range = `Assoc [("uri", `String uri); ("range", json_range range)]

  let parse_json_position = function
    | `Assoc _ as json -> (
        match (json_int_member "line" json, json_int_member "character" json) with
        | Some line, Some character -> Some { line; character }
        | _ -> None
      )
    | _ -> None

  let parse_json_range = function
    | `Assoc _ as json -> (
        match (json_member "start" json, json_member "end" json) with
        | Some start_json, Some end_json ->
            Option.bind (parse_json_position start_json) (fun start_pos ->
                Option.map (fun end_pos -> { start_pos; end_pos }) (parse_json_position end_json)
            )
        | _ -> None
      )
    | _ -> None

  let canonical_file path = try Unix.realpath path with Unix.Unix_error _ | Sys_error _ -> path

  let offset_of_position text position =
    let len = String.length text in
    let rec loop line offset =
      if line >= position.line then min len (offset + position.character)
      else (
        match String.index_from_opt text offset '\n' with Some newline -> loop (line + 1) (newline + 1) | None -> len
      )
    in
    loop 0 0

  let position_of_offset text offset =
    let offset = max 0 (min offset (String.length text)) in
    let rec loop line line_start i =
      if i >= offset then { line; character = offset - line_start }
      else if text.[i] = '\n' then loop (line + 1) (i + 1) (i + 1)
      else loop line line_start (i + 1)
    in
    loop 0 0 0

  let lsp_position_of_lexing_position position =
    {
      line = max 0 (position.Lexing.pos_lnum - 1);
      character = max 0 (position.Lexing.pos_cnum - position.Lexing.pos_bol);
    }

  let range_of_lexing_positions start_pos end_pos =
    { start_pos = lsp_position_of_lexing_position start_pos; end_pos = lsp_position_of_lexing_position end_pos }

  let location_of_parse_ast_loc loc =
    match Sail.Reporting.simp_loc loc with
    | Some (start_pos, end_pos) when start_pos.Lexing.pos_fname <> "" ->
        Some (uri_of_path start_pos.Lexing.pos_fname, range_of_lexing_positions start_pos end_pos)
    | _ -> None

  let lexing_position_of_lsp_position path text position =
    let offset = offset_of_position text position in
    let actual = position_of_offset text offset in
    { Lexing.pos_fname = path; pos_lnum = actual.line + 1; pos_bol = offset - actual.character; pos_cnum = offset }

  let parse_ast_loc_of_lsp_position path text position =
    let cursor = lexing_position_of_lsp_position path text position in
    Sail.Parse_ast.Range (cursor, cursor)

  let fallback_range = { start_pos = { line = 0; character = 0 }; end_pos = { line = 0; character = 1 } }

  let diagnostic_file_of_lexing_position fallback_path position =
    if position.Lexing.pos_fname = "" then fallback_path else canonical_file position.Lexing.pos_fname

  let diagnostic_file_and_range_of_loc fallback_path loc =
    match Sail.Reporting.simp_loc loc with
    | Some (start_pos, end_pos) ->
        (diagnostic_file_of_lexing_position fallback_path start_pos, range_of_lexing_positions start_pos end_pos)
    | None -> (fallback_path, fallback_range)

  let diagnostic_file_and_range_of_position fallback_path position =
    (diagnostic_file_of_lexing_position fallback_path position, range_of_lexing_positions position position)
end

let json_position = Source_location.json_position

let json_range = Source_location.json_range

let location_json = Source_location.location_json

let parse_json_position = Source_location.parse_json_position

let parse_json_range = Source_location.parse_json_range

let canonical_file = Source_location.canonical_file

let send_json json =
  let body = Json.to_string json in
  Printf.printf "Content-Length: %d\r\n\r\n%s%!" (String.length body) body

let response id result = send_json (`Assoc [("jsonrpc", `String jsonrpc); ("id", id); ("result", result)])

let error_response id code message =
  send_json
    (`Assoc
       [("jsonrpc", `String jsonrpc); ("id", id); ("error", `Assoc [("code", `Int code); ("message", `String message)])]
    )

let notification method_ params =
  send_json (`Assoc [("jsonrpc", `String jsonrpc); ("method", `String method_); ("params", params)])

let show_message message = notification "window/showMessage" (`Assoc [("type", `Int 3); ("message", `String message)])

let read_message () =
  let rec read_headers content_length =
    match input_line stdin with
    | exception End_of_file -> None
    | line ->
        let line = drop_trailing_cr line in
        if line = "" then content_length
        else (
          let lower = String.lowercase_ascii line in
          if starts_with ~prefix:"content-length:" lower then (
            let value = String.sub line 15 (String.length line - 15) |> String.trim |> int_of_string_opt in
            read_headers value
          )
          else read_headers content_length
        )
  in
  match read_headers None with None -> None | Some len -> Some (really_input_string stdin len)

let read_file path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () ->
      let len = in_channel_length channel in
      really_input_string channel len
    )

let write_file path contents =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out_noerr channel) (fun () -> output_string channel contents)

let read_channel_all channel =
  let buf = Buffer.create 1024 in
  let chunk = Bytes.create 4096 in
  let rec loop () =
    match input channel chunk 0 (Bytes.length chunk) with
    | 0 -> Buffer.contents buf
    | n ->
        Buffer.add_subbytes buf chunk 0 n;
        loop ()
  in
  loop ()

let document_text uri =
  match Hashtbl.find_opt text_documents uri with
  | Some text -> Some text
  | None -> (
      let path = path_of_uri uri in
      try Some (read_file path) with Sys_error _ -> None
    )

let lines_of_text text = String.split_on_char '\n' text |> List.map drop_trailing_cr

let offset_of_position = Source_location.offset_of_position

let position_of_offset = Source_location.position_of_offset

let lsp_position_of_lexing_position = Source_location.lsp_position_of_lexing_position

let lsp_range_of_lexing_positions = Source_location.range_of_lexing_positions

let location_of_parse_ast_loc = Source_location.location_of_parse_ast_loc

let lexing_position_of_lsp_position = Source_location.lexing_position_of_lsp_position

let parse_ast_loc_of_lsp_position = Source_location.parse_ast_loc_of_lsp_position

module LspCursorScanner = Sail.Ast_util.Scanner (struct
  type t = Sail.Parse_ast.l

  let subloc cursor loc =
    match (Sail.Reporting.simp_loc cursor, Sail.Reporting.simp_loc loc) with
    | Some (cursor_pos, _), Some (start_pos, end_pos) ->
        canonical_file cursor_pos.Lexing.pos_fname = canonical_file start_pos.Lexing.pos_fname
        && cursor_pos.Lexing.pos_cnum >= start_pos.Lexing.pos_cnum
        && cursor_pos.Lexing.pos_cnum <= end_pos.Lexing.pos_cnum
    | _ -> false
end)

let is_space = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false

let is_digit = function '0' .. '9' -> true | _ -> false

let is_ident_char = function 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' | '\'' | '#' -> true | _ -> false

let is_symbolic_char = function
  | '!' | '$' | '%' | '&' | '*' | '+' | '-' | '.' | '/' | ':' | '<' | '=' | '>' | '?' | '@' | '^' | '|' | '~' -> true
  | _ -> false

let read_token line i =
  let len = String.length line in
  let rec skip i = if i < len && is_space line.[i] then skip (i + 1) else i in
  let i = skip i in
  if i >= len then None
  else (
    let is_token_char = if is_symbolic_char line.[i] then is_symbolic_char else is_ident_char in
    let rec take j = if j < len && is_token_char line.[j] then take (j + 1) else j in
    let j = take i in
    if i = j then None else Some (String.sub line i (j - i), i, j)
  )

let rec tokens_from line i =
  match read_token line i with None -> [] | Some (token, start, stop) -> (token, start, stop) :: tokens_from line stop

let keyword_symbol_kind = function
  | "val" | "function" | "mapping" | "operator" -> 12
  | "type" | "struct" | "union" | "bitfield" -> 23
  | "enum" -> 10
  | "register" | "let" | "constant" -> 13
  | _ -> 13

let symbol_from_tokens uri line_no line tokens =
  let tokens = match tokens with ("private", _, _) :: rest | ("default", _, _) :: rest -> rest | rest -> rest in
  let symbol_name keyword name start stop =
    let range =
      { start_pos = { line = line_no; character = 0 }; end_pos = { line = line_no; character = String.length line } }
    in
    let selection_range =
      { start_pos = { line = line_no; character = start }; end_pos = { line = line_no; character = stop } }
    in
    Some { name; kind = keyword_symbol_kind keyword; detail = keyword; uri; range; selection_range }
  in
  match tokens with
  | (("//" | "/*"), _, _) :: _ -> None
  | ("scattered", _, _) :: (kind, _, _) :: (name, start, stop) :: _ -> symbol_name ("scattered " ^ kind) name start stop
  | ("let", _, _) :: ("rec", _, _) :: (name, start, stop) :: _ -> symbol_name "let" name start stop
  | ("function", _, _) :: ("clause", _, _) :: (name, start, stop) :: _ -> symbol_name "function" name start stop
  | ( ( ( "val" | "function" | "mapping" | "register" | "type" | "struct" | "union" | "enum" | "bitfield" | "operator"
        | "constant" ) as keyword
      ),
      _,
      _
    )
    :: (name, start, stop)
    :: _ ->
      symbol_name keyword name start stop
  | _ -> None

let document_symbols uri text =
  lines_of_text text
  |> List.mapi (fun line_no line -> symbol_from_tokens uri line_no line (tokens_from line 0))
  |> List.filter_map Fun.id

type semantic_token = { token_line : int; token_start : int; token_length : int; token_type : int }

let semantic_token_types =
  [
    "namespace";
    "type";
    "class";
    "enum";
    "interface";
    "struct";
    "typeParameter";
    "parameter";
    "variable";
    "property";
    "enumMember";
    "event";
    "function";
    "method";
    "macro";
    "keyword";
    "modifier";
    "comment";
    "string";
    "number";
    "regexp";
    "operator";
  ]

let semantic_token_type_index name =
  let rec loop i = function [] -> 0 | token_type :: rest -> if token_type = name then i else loop (i + 1) rest in
  loop 0 semantic_token_types

let sail_keywords =
  [
    "as";
    "assert";
    "bitfield";
    "by";
    "cast";
    "constant";
    "default";
    "else";
    "end";
    "enum";
    "foreach";
    "function";
    "if";
    "in";
    "let";
    "mapping";
    "match";
    "operator";
    "outcome";
    "overload";
    "private";
    "register";
    "repeat";
    "scattered";
    "sizeof";
    "struct";
    "then";
    "type";
    "union";
    "val";
    "var";
    "while";
  ]

let semantic_type_of_symbol_detail = function
  | "function" | "let" | "mapping" | "operator" -> "function"
  | "type" | "struct" | "union" | "bitfield" -> "type"
  | "enum" -> "enum"
  | "register" -> "property"
  | _ -> "variable"

let semantic_symbol_table uri text =
  let table = Hashtbl.create 128 in
  document_symbols uri text
  |> List.iter (fun symbol -> Hashtbl.replace table symbol.name (semantic_type_of_symbol_detail symbol.detail));
  table

let add_semantic_token line start stop token_type acc =
  if stop <= start then acc
  else
    {
      token_line = line;
      token_start = start;
      token_length = stop - start;
      token_type = semantic_token_type_index token_type;
    }
    :: acc

let semantic_tokens_for_line symbol_table line_no line =
  let len = String.length line in
  let rec scan i acc =
    if i >= len then acc
    else (
      match line.[i] with
      | c when is_space c -> scan (i + 1) acc
      | '/' when i + 1 < len && line.[i + 1] = '/' -> add_semantic_token line_no i len "comment" acc
      | '"' ->
          let rec string_end j escaped =
            if j >= len then len
            else if escaped then string_end (j + 1) false
            else (match line.[j] with '\\' -> string_end (j + 1) true | '"' -> j + 1 | _ -> string_end (j + 1) false)
          in
          let stop = string_end (i + 1) false in
          scan stop (add_semantic_token line_no i stop "string" acc)
      | '0' .. '9' ->
          let rec take j = if j < len && (is_digit line.[j] || line.[j] = '_') then take (j + 1) else j in
          let stop = take (i + 1) in
          scan stop (add_semantic_token line_no i stop "number" acc)
      | c when is_ident_char c ->
          let rec take j = if j < len && is_ident_char line.[j] then take (j + 1) else j in
          let stop = take (i + 1) in
          let word = String.sub line i (stop - i) in
          let acc =
            if List.mem word sail_keywords then add_semantic_token line_no i stop "keyword" acc
            else (
              match Hashtbl.find_opt symbol_table word with
              | Some token_type -> add_semantic_token line_no i stop token_type acc
              | None -> acc
            )
          in
          scan stop acc
      | c when is_symbolic_char c ->
          let rec take j = if j < len && is_symbolic_char line.[j] then take (j + 1) else j in
          let stop = take (i + 1) in
          scan stop (add_semantic_token line_no i stop "operator" acc)
      | _ -> scan (i + 1) acc
    )
  in
  scan 0 []

let semantic_tokens uri text =
  let symbol_table = semantic_symbol_table uri text in
  lines_of_text text
  |> List.mapi (semantic_tokens_for_line symbol_table)
  |> List.concat |> List.rev
  |> List.sort (fun a b ->
      match compare a.token_line b.token_line with 0 -> compare a.token_start b.token_start | n -> n
  )

let encode_semantic_tokens tokens =
  let rec loop prev_line prev_start acc = function
    | [] -> List.rev acc
    | token :: rest ->
        let delta_line = token.token_line - prev_line in
        let delta_start = if delta_line = 0 then token.token_start - prev_start else token.token_start in
        let encoded = [`Int delta_line; `Int delta_start; `Int token.token_length; `Int token.token_type; `Int 0] in
        loop token.token_line token.token_start (List.rev_append encoded acc) rest
  in
  loop 0 0 [] tokens

let symbol_json symbol =
  `Assoc
    [
      ("name", `String symbol.name);
      ("detail", `String symbol.detail);
      ("kind", `Int symbol.kind);
      ("range", json_range symbol.range);
      ("selectionRange", json_range symbol.selection_range);
    ]

type workspace_document = { doc_uri : string; doc_path : string; doc_text : string }

let is_sail_source_path path = Filename.check_suffix path ".sail"

let is_sail_project_path path = Filename.check_suffix path ".sail_project"

let ignored_workspace_dir name =
  List.mem name [".git"; "_build"; ".worktrees"; "node_modules"; ".agent-deck"; ".agents"; ".claude"]

let rec collect_files_by_suffix suffix dir =
  let entries = try Sys.readdir dir |> Array.to_list with Sys_error _ -> [] in
  List.concat_map
    (fun name ->
      let path = Filename.concat dir name in
      try
        if Sys.is_directory path then if ignored_workspace_dir name then [] else collect_files_by_suffix suffix path
        else if Filename.check_suffix path suffix then [path]
        else []
      with Sys_error _ -> []
    )
    entries

let collect_sail_files dir = collect_files_by_suffix ".sail" dir

let workspace_file_paths () =
  let root = root_or_cwd () in
  if Sys.file_exists root then collect_sail_files root else []

let project_files_in_dir dir =
  let entries = try Sys.readdir dir |> Array.to_list with Sys_error _ -> [] in
  entries |> List.filter is_sail_project_path
  |> List.map (Filename.concat dir)
  |> List.filter (fun path -> try not (Sys.is_directory path) with Sys_error _ -> false)

let discover_project_files_for path =
  let rec loop dir =
    match project_files_in_dir dir with
    | [] ->
        let parent = Filename.dirname dir in
        if parent = dir then [] else loop parent
    | projects -> projects
  in
  loop (Filename.dirname path)

let discover_project_file_for path = match discover_project_files_for path with [project] -> Some project | _ -> None

let workspace_documents ?current_uri ?current_text () =
  let seen = Hashtbl.create 128 in
  let add_uri uri text docs =
    if Hashtbl.mem seen uri then docs
    else (
      Hashtbl.add seen uri ();
      { doc_uri = uri; doc_path = path_of_uri uri; doc_text = text } :: docs
    )
  in
  let docs = match (current_uri, current_text) with Some uri, Some text -> add_uri uri text [] | _ -> [] in
  let docs = Hashtbl.fold (fun uri text docs -> add_uri uri text docs) text_documents docs in
  let docs =
    List.fold_left
      (fun docs path ->
        let uri = uri_of_path path in
        if Hashtbl.mem seen uri then docs
        else (
          try
            let text = read_file path in
            add_uri uri text docs
          with Sys_error _ -> docs
        )
      )
      docs (workspace_file_paths ())
  in
  List.rev docs

let line_at text line_no = List.nth_opt (lines_of_text text) line_no

let symbol_source_line text symbol = line_at text symbol.range.start_pos.line

let type_annotation_from_line line =
  match String.index_opt line ':' with
  | None -> None
  | Some colon ->
      let ty = String.sub line (colon + 1) (String.length line - colon - 1) |> String.trim in
      if ty = "" then None else Some ty

let source_type_for_symbol text symbol =
  match symbol.detail with
  | "val" | "register" -> Option.bind (symbol_source_line text symbol) type_annotation_from_line
  | _ -> None

type source_type_entry = { source_symbol : symbol; source_type : string }

let source_type_entry_json entry =
  `Assoc
    [
      ("name", `String entry.source_symbol.name);
      ("kind", `String entry.source_symbol.detail);
      ("type", `String entry.source_type);
      ("location", location_json entry.source_symbol.uri entry.source_symbol.selection_range);
      ("source", `String "source");
    ]

let source_type_entry_for_name uri text name =
  workspace_documents ~current_uri:uri ~current_text:text ()
  |> List.find_map (fun doc ->
      document_symbols doc.doc_uri doc.doc_text
      |> List.find_map (fun symbol ->
          if symbol.name = name then
            Option.map
              (fun source_type -> { source_symbol = symbol; source_type })
              (source_type_for_symbol doc.doc_text symbol)
          else None
      )
  )

let semantic_workspace_symbol_table uri text =
  let table = Hashtbl.create 256 in
  workspace_documents ~current_uri:uri ~current_text:text ()
  |> List.iter (fun doc ->
      document_symbols doc.doc_uri doc.doc_text
      |> List.iter (fun symbol -> Hashtbl.replace table symbol.name (semantic_type_of_symbol_detail symbol.detail))
  );
  table

let semantic_tokens_with_workspace uri text =
  let symbol_table = semantic_workspace_symbol_table uri text in
  lines_of_text text
  |> List.mapi (semantic_tokens_for_line symbol_table)
  |> List.concat |> List.rev
  |> List.sort (fun a b ->
      match compare a.token_line b.token_line with 0 -> compare a.token_start b.token_start | n -> n
  )

let symbol_preference = function "function" | "let" -> 0 | "mapping" -> 1 | "val" -> 2 | _ -> 3

let choose_symbol name symbols =
  symbols
  |> List.filter (fun symbol -> symbol.name = name)
  |> List.sort (fun a b -> compare (symbol_preference a.detail) (symbol_preference b.detail))
  |> List.find_opt (fun _ -> true)

let sail_symbol_location uri text name =
  let current_symbols = document_symbols uri text in
  match choose_symbol name current_symbols with
  | Some symbol -> Some (symbol.uri, symbol.selection_range)
  | None ->
      workspace_documents ~current_uri:uri ~current_text:text ()
      |> List.filter_map (fun doc -> choose_symbol name (document_symbols doc.doc_uri doc.doc_text))
      |> List.sort (fun a b -> compare (symbol_preference a.detail) (symbol_preference b.detail))
      |> List.find_opt (fun _ -> true)
      |> Option.map (fun symbol -> (symbol.uri, symbol.selection_range))

let lowercase_contains haystack needle =
  let haystack = String.lowercase_ascii haystack in
  let needle = String.lowercase_ascii needle in
  let haystack_len = String.length haystack in
  let needle_len = String.length needle in
  needle_len = 0
  ||
  let rec loop i = i + needle_len <= haystack_len && (String.sub haystack i needle_len = needle || loop (i + 1)) in
  loop 0

let lowercase_starts_with haystack needle =
  let haystack = String.lowercase_ascii haystack in
  let needle = String.lowercase_ascii needle in
  let needle_len = String.length needle in
  needle_len = 0 || (String.length haystack >= needle_len && String.sub haystack 0 needle_len = needle)

let symbol_information_json symbol =
  `Assoc
    [
      ("name", `String symbol.name);
      ("kind", `Int symbol.kind);
      ("location", location_json symbol.uri symbol.selection_range);
      ("containerName", `String symbol.detail);
    ]

let handle_workspace_symbol id params =
  let query = json_string_member "query" params |> Option.value ~default:"" in
  let symbols =
    workspace_documents ()
    |> List.concat_map (fun doc -> document_symbols doc.doc_uri doc.doc_text)
    |> List.filter (fun symbol -> lowercase_contains symbol.name query || lowercase_contains symbol.detail query)
    |> List.map symbol_information_json
  in
  response id (`List symbols)

let sail_identifier_at line name start =
  let name_len = String.length name in
  start + name_len <= String.length line
  && String.sub line start name_len = name
  && (start = 0 || not (is_ident_char line.[start - 1]))
  && (start + name_len = String.length line || not (is_ident_char line.[start + name_len]))

let reference_offsets_in_line line name =
  let name_len = String.length name in
  let rec search i acc =
    if name_len = 0 || i + name_len > String.length line then List.rev acc
    else if sail_identifier_at line name i then search (i + name_len) (i :: acc)
    else search (i + 1) acc
  in
  search 0 []

let identifier_ranges_in_document doc =
  let in_block_comment = ref false in
  let range_at line_no start stop =
    {
      loc_uri = doc.doc_uri;
      loc_range = { start_pos = { line = line_no; character = start }; end_pos = { line = line_no; character = stop } };
    }
  in
  let scan_line line_no line =
    let len = String.length line in
    let rec block_comment_end i =
      if i + 1 >= len then None
      else if line.[i] = '*' && line.[i + 1] = '/' then Some (i + 2)
      else block_comment_end (i + 1)
    in
    let rec string_end i escaped =
      if i >= len then len
      else if escaped then string_end (i + 1) false
      else (match line.[i] with '\\' -> string_end (i + 1) true | '"' -> i + 1 | _ -> string_end (i + 1) false)
    in
    let rec scan i acc =
      if i >= len then List.rev acc
      else if !in_block_comment then (
        match block_comment_end i with
        | Some stop ->
            in_block_comment := false;
            scan stop acc
        | None -> List.rev acc
      )
      else (
        match line.[i] with
        | '/' when i + 1 < len && line.[i + 1] = '/' -> List.rev acc
        | '/' when i + 1 < len && line.[i + 1] = '*' -> (
            match block_comment_end (i + 2) with
            | Some stop -> scan stop acc
            | None ->
                in_block_comment := true;
                List.rev acc
          )
        | '"' -> scan (string_end (i + 1) false) acc
        | c when is_ident_char c ->
            let rec take j = if j < len && is_ident_char line.[j] then take (j + 1) else j in
            let stop = take (i + 1) in
            let word = String.sub line i (stop - i) in
            scan stop ((word, range_at line_no i stop) :: acc)
        | _ -> scan (i + 1) acc
      )
    in
    scan 0 []
  in
  lines_of_text doc.doc_text |> List.mapi scan_line |> List.concat

let reference_ranges_in_document doc name =
  identifier_ranges_in_document doc
  |> List.filter_map (fun (word, reference) -> if word = name then Some reference else None)

let references_in_document doc name =
  reference_ranges_in_document doc name
  |> List.map (fun reference -> location_json reference.loc_uri reference.loc_range)

let word_at_position text position =
  let lines = lines_of_text text in
  match List.nth_opt lines position.line with
  | None -> None
  | Some line ->
      let len = String.length line in
      let pos = min position.character len in
      let rec left i = if i > 0 && is_ident_char line.[i - 1] then left (i - 1) else i in
      let rec right i = if i < len && is_ident_char line.[i] then right (i + 1) else i in
      let start = left pos in
      let stop = right pos in
      if start = stop then None else Some (String.sub line start (stop - start))

let position_from_json json =
  match (json_int_member "line" json, json_int_member "character" json) with
  | Some line, Some character -> Some { line; character }
  | _ -> None

let text_document_uri params =
  match json_member "textDocument" params with
  | Some text_document -> json_string_member "uri" text_document
  | None -> None

let position_param params = match json_member "position" params with Some pos -> position_from_json pos | None -> None

let range_start_param params =
  match json_member "range" params with
  | Some range -> (
      match json_member "start" range with Some pos -> position_from_json pos | None -> None
    )
  | None -> None

let configure_from_initialize params =
  ( match json_string_member "rootUri" params with
  | Some uri -> root_path := Some (path_of_uri uri)
  | None -> (
      match json_string_member "rootPath" params with Some path -> root_path := Some path | None -> ()
    )
  );
  match json_member "initializationOptions" params with
  | Some options -> (
      clear_compiler_env_cache ();
      let configure_optional_string keys set =
        let rec loop = function
          | [] -> ()
          | key :: keys -> (
              match json_string_member key options with Some value -> set value | None -> loop keys
            )
        in
        loop keys
      in
      configure_optional_string ["cOutput"; "cOutputFile"] (fun path -> configured_c_output := Some path);
      configure_optional_string ["cMap"; "cMapFile"; "cSidecar"; "cSidecarFile"] (fun path ->
          configured_c_map := Some path
      );
      configure_optional_string ["docInfo"; "docInfoFile"; "docinfo"; "docinfoFile"] (fun path ->
          configured_docinfo := Some path
      );
      configure_optional_string ["artifactIndex"; "artifactIndexFile"; "artifacts"; "artifactsFile"] (fun path ->
          configured_artifact_index := Some path
      );
      configure_optional_string ["sail"; "sailPath"; "sailExecutable"; "executablePath"] (fun path ->
          configured_sail_executable := path
      );
      configure_optional_string ["project"; "projectFile"; "sailProject"] (fun path -> configured_project := Some path);
      ( match json_string_list_member "modules" options with
      | Some modules ->
          configured_modules_explicit := true;
          configured_modules := modules
      | None -> ()
      );
      ( match json_string_list_member "projectModules" options with
      | Some modules ->
          configured_modules_explicit := true;
          configured_modules := modules
      | None -> ()
      );
      ( match json_bool_member "allModules" options with
      | Some enabled ->
          configured_all_modules_explicit := true;
          configured_all_modules := enabled
      | None -> ()
      );
      match json_bool_member "diagnostics" options with Some enabled -> diagnostics_enabled := enabled | None -> ()
    )
  | None -> ()

let absolutize_against_root path =
  if Filename.is_relative path then (
    match !root_path with Some root -> Filename.concat root path | None -> Filename.concat (Sys.getcwd ()) path
  )
  else path

let absolutize_against_dir dir path = if Filename.is_relative path then Filename.concat dir path else path

type artifact_index = {
  artifact_index_path : string;
  artifact_c_output : string option;
  artifact_c_map : string option;
  artifact_docinfo : string option;
  artifact_project : string option;
  artifact_project_modules : string list option;
  artifact_project_all_modules : bool option;
}

let artifact_index_names = ["sail.lsp.json"; ".sail_lsp.json"; "out.sail_lsp.json"; "out.sail_artifacts.json"]

let dedupe_preserve_order paths =
  let seen = Hashtbl.create 8 in
  List.filter
    (fun path ->
      if Hashtbl.mem seen path then false
      else (
        Hashtbl.add seen path ();
        true
      )
    )
    paths

let collect_artifact_index_files dir =
  let rec loop dir =
    let entries = try Sys.readdir dir |> Array.to_list with Sys_error _ -> [] in
    List.concat_map
      (fun name ->
        let path = Filename.concat dir name in
        try
          if Sys.is_directory path then if ignored_workspace_dir name then [] else loop path
          else if List.mem name artifact_index_names then [path]
          else []
        with Sys_error _ -> []
      )
      entries
  in
  loop dir

let artifact_index_candidates () =
  match !configured_artifact_index with
  | Some path -> [absolutize_against_root path]
  | None ->
      let root = root_or_cwd () in
      let root_candidates = List.map (Filename.concat root) artifact_index_names in
      dedupe_preserve_order (root_candidates @ collect_artifact_index_files root)

let json_string_member_any keys json = List.find_map (fun key -> json_string_member key json) keys

let json_bool_member_any keys json = List.find_map (fun key -> json_bool_member key json) keys

let json_string_list_member_any keys json = List.find_map (fun key -> json_string_list_member key json) keys

let supported_artifact_index_schema json =
  match json_string_member "schema" json with
  | None -> true
  | Some ("sail.lsp.artifacts" | "sail.artifacts") -> true
  | Some _ -> false

let artifact_payload_sets json =
  match json_member "artifacts" json with
  | Some (`List artifacts) ->
      List.filter_map (function `Assoc _ as artifact -> Some [artifact; json] | _ -> None) artifacts
  | Some (`Assoc _ as artifacts) -> [[artifacts; json]]
  | _ -> [[json]]

let artifact_string dir keys payloads =
  List.find_map (json_string_member_any keys) payloads |> Option.map (absolutize_against_dir dir)

let artifact_string_list keys payloads = List.find_map (json_string_list_member_any keys) payloads

let artifact_bool keys payloads = List.find_map (json_bool_member_any keys) payloads

let parse_artifact_index path =
  try
    let json = Json.from_file path in
    if not (supported_artifact_index_schema json) then []
    else (
      let dir = Filename.dirname path in
      artifact_payload_sets json
      |> List.map (fun payloads ->
          {
            artifact_index_path = path;
            artifact_c_output = artifact_string dir ["cOutput"; "cOutputFile"; "cFile"] payloads;
            artifact_c_map = artifact_string dir ["cMap"; "cMapFile"; "cSidecar"; "cSidecarFile"] payloads;
            artifact_docinfo = artifact_string dir ["docinfo"; "docinfoFile"; "docInfo"; "docInfoFile"] payloads;
            artifact_project = artifact_string dir ["project"; "projectFile"; "sailProject"] payloads;
            artifact_project_modules = artifact_string_list ["modules"; "projectModules"] payloads;
            artifact_project_all_modules = artifact_bool ["allModules"; "projectAllModules"] payloads;
          }
      )
    )
  with Sys_error _ | Yojson.Json_error _ -> []

let artifact_indexes () = List.concat_map parse_artifact_index (artifact_index_candidates ())

let artifact_values field = List.filter_map field (artifact_indexes ())

let artifact_c_outputs () = artifact_values (fun index -> index.artifact_c_output)

let artifact_c_maps () = artifact_values (fun index -> index.artifact_c_map)

let artifact_docinfos () = artifact_values (fun index -> index.artifact_docinfo)

let artifact_project () = List.find_map (fun index -> index.artifact_project) (artifact_indexes ())

let same_file a b = canonical_file a = canonical_file b

let configured_file_matches configured path =
  match !configured with Some candidate -> same_file (absolutize_against_root candidate) path | None -> false

let is_artifact_manifest_path path =
  let name = Filename.basename path in
  List.mem name artifact_index_names
  || Filename.check_suffix name ".sail_lsp.json"
  || Filename.check_suffix name ".sail_artifacts.json"
  || configured_file_matches configured_artifact_index path

let workspace_change_invalidates_cache path =
  is_sail_source_path path || is_sail_project_path path || is_artifact_manifest_path path
  || Filename.check_suffix path ".symbols.json"
  || Filename.check_suffix path ".docinfo.json"
  || Filename.check_suffix path ".c" || Filename.check_suffix path ".cpp"
  || Filename.basename path = "doc.json"
  || configured_file_matches configured_c_output path
  || configured_file_matches configured_c_map path
  || configured_file_matches configured_docinfo path

let workspace_change_affects_diagnostics path =
  is_sail_source_path path || is_sail_project_path path || is_artifact_manifest_path path

let artifact_c_output_for_map c_map =
  artifact_indexes ()
  |> List.find_map (fun index ->
      match (index.artifact_c_map, index.artifact_c_output) with
      | Some candidate_map, Some c_output when same_file candidate_map c_map -> Some c_output
      | _ -> None
  )

let artifact_project_modules () = List.find_map (fun index -> index.artifact_project_modules) (artifact_indexes ())

let artifact_project_all_modules () =
  List.find_map (fun index -> index.artifact_project_all_modules) (artifact_indexes ())

let artifact_index_cache_fragment () =
  artifact_indexes ()
  |> List.map (fun index ->
      String.concat "\001"
        [
          index.artifact_index_path;
          Option.value ~default:"" index.artifact_c_output;
          Option.value ~default:"" index.artifact_c_map;
          Option.value ~default:"" index.artifact_docinfo;
          Option.value ~default:"" index.artifact_project;
          (match index.artifact_project_modules with Some modules -> String.concat "," modules | None -> "");
          (match index.artifact_project_all_modules with Some value -> string_of_bool value | None -> "");
        ]
  )
  |> String.concat "\002"

let configured_project_for_path path =
  match !configured_project with
  | Some project -> Some (absolutize_against_root project)
  | None -> (
      match artifact_project () with Some project -> Some project | None -> discover_project_file_for path
    )

let configured_project_modules () =
  if !configured_modules_explicit || !configured_modules <> [] then Some !configured_modules
  else if !configured_all_modules_explicit then if !configured_all_modules then None else Some []
  else (
    match artifact_project_modules () with
    | Some modules -> Some modules
    | None -> (
        match artifact_project_all_modules () with
        | Some true -> None
        | Some false -> Some []
        | None -> if !configured_all_modules then None else Some []
      )
  )

let rec find_repo_sail_dir_from dir =
  let candidate = Filename.concat dir "lib" in
  if Sys.file_exists (Filename.concat candidate "prelude.sail") then Some dir
  else (
    let parent = Filename.dirname dir in
    if parent = dir then None else find_repo_sail_dir_from parent
  )

let compiler_default_sail_dir () =
  let installed_prelude = Filename.concat Locations.sail_dir "lib/prelude.sail" in
  if Sys.file_exists installed_prelude then Locations.sail_dir
  else
    [
      root_or_cwd ();
      server_launch_cwd;
      Sys.getcwd ();
      Filename.concat server_launch_cwd "..";
      Filename.concat server_launch_cwd "../..";
    ]
    |> List.find_map find_repo_sail_dir_from
    |> Option.value ~default:Locations.sail_dir

let compiler_env_cache_key path =
  match configured_project_for_path path with
  | Some project -> (
      "project:" ^ project ^ ":modules:"
      ^ match configured_project_modules () with None -> "*" | Some modules -> String.concat "," modules
    )
  | None -> "file:" ^ path

let load_compiler_model_uncached path =
  let _, compiler_ast, compiler_env, _ =
    match configured_project_for_path path with
    | Some project ->
        let modules = configured_project_modules () in
        Sail.Frontend.load_project ?modules (compiler_default_sail_dir ()) [project]
    | None -> Sail.Frontend.load_files (compiler_default_sail_dir ()) [] Sail.Type_check.initial_env [path]
  in
  { compiler_ast; compiler_env }

let load_compiler_model path =
  if not (is_sail_source_path path && Sys.file_exists path) then None
  else (
    let key = compiler_env_cache_key path in
    if Hashtbl.mem compiler_model_failure_cache key then None
    else (
      match Hashtbl.find_opt compiler_model_cache key with
      | Some model -> Some model
      | None -> (
          try
            let model = load_compiler_model_uncached path in
            Hashtbl.replace compiler_model_cache key model;
            Some model
          with _ ->
            Hashtbl.replace compiler_model_failure_cache key ();
            None
        )
    )
  )

let load_compiler_env path = Option.map (fun model -> model.compiler_env) (load_compiler_model path)

type compiler_type_entry = {
  compiler_name : string;
  compiler_kind : string;
  compiler_type : string;
  compiler_location : (string * range) option;
}

let compiler_doc_to_string doc = Sail.Pretty_print_sail.Document.to_string doc |> String.trim

let compiler_type_scheme_string typq typ =
  Sail.Ast_util.mk_typschm typq typ |> Sail.Pretty_print_sail.doc_typschm |> compiler_doc_to_string

let compiler_type_string typ = Sail.Pretty_print_sail.doc_typ typ |> compiler_doc_to_string

let source_kind_for_name uri text name =
  let current_symbols = document_symbols uri text in
  match choose_symbol name current_symbols with
  | Some symbol -> Some symbol.detail
  | None ->
      workspace_documents ~current_uri:uri ~current_text:text ()
      |> List.find_map (fun doc ->
          Option.map (fun symbol -> symbol.detail) (choose_symbol name (document_symbols doc.doc_uri doc.doc_text))
      )

let compiler_kind_for_val env id fallback =
  match fallback with
  | Some kind -> kind
  | None when Sail.Type_check.Env.is_mapping id env -> "mapping"
  | None when Sail.Type_check.Env.is_union_constructor id env -> "constructor"
  | None when Sail.Type_check.is_enum_member id env -> "enum member"
  | None when Sail.Ast_compare.IdSet.mem id (Sail.Type_check.Env.get_defined_val_specs env) -> "function"
  | None -> "val"

let compiler_type_entry_for_name uri text name =
  let path = path_of_uri uri in
  match load_compiler_env path with
  | None -> None
  | Some env ->
      let id = Sail.Ast_util.mk_id name in
      let fallback_kind = source_kind_for_name uri text name in
      let location = sail_symbol_location uri text name in
      if Sail.Type_check.Env.is_register id env then (
        try
          Some
            {
              compiler_name = name;
              compiler_kind = "register";
              compiler_type = compiler_type_string (Sail.Type_check.Env.get_register id env);
              compiler_location = location;
            }
        with _ -> None
      )
      else if Sail.Type_check.Env.has_val_spec id env then (
        try
          let typq, typ = Sail.Type_check.Env.get_val_spec id env in
          Some
            {
              compiler_name = name;
              compiler_kind = compiler_kind_for_val env id fallback_kind;
              compiler_type = compiler_type_scheme_string typq typ;
              compiler_location = location;
            }
        with _ -> None
      )
      else None

let compiler_type_entry_json entry =
  let fields =
    [
      ("name", `String entry.compiler_name);
      ("kind", `String entry.compiler_kind);
      ("type", `String entry.compiler_type);
      ("source", `String "compiler");
    ]
  in
  let fields =
    match entry.compiler_location with
    | Some (uri, range) -> ("location", location_json uri range) :: fields
    | None -> fields
  in
  `Assoc fields

let compiler_type_entry_at_position uri text position =
  let path = path_of_uri uri in
  match load_compiler_model path with
  | None -> None
  | Some model -> (
      let cursor = parse_ast_loc_of_lsp_position path text position in
      match LspCursorScanner.find_annot_ast cursor model.compiler_ast with
      | None -> None
      | Some (loc, annot) -> (
          match Sail.Type_check.destruct_tannot annot with
          | None -> None
          | Some (_, typ) -> (
              try
                let name = word_at_position text position |> Option.value ~default:"expression" in
                Some
                  {
                    compiler_name = name;
                    compiler_kind = "expression";
                    compiler_type = compiler_type_string typ;
                    compiler_location = location_of_parse_ast_loc loc;
                  }
              with _ -> None
            )
        )
    )

type compiler_lvar_kind = Compiler_local | Compiler_register | Compiler_enum | Compiler_unbound

let compiler_lvar_kind_at_position uri text position name =
  let path = path_of_uri uri in
  match load_compiler_model path with
  | None -> None
  | Some model -> (
      let cursor = parse_ast_loc_of_lsp_position path text position in
      match LspCursorScanner.find_annot_ast cursor model.compiler_ast with
      | None -> None
      | Some (_, annot) -> (
          match Sail.Type_check.destruct_tannot annot with
          | None -> None
          | Some (env, _) -> (
              match Sail.Type_check.Env.lookup_id (Sail.Ast_util.mk_id name) env with
              | Sail.Ast_util.Local (_, _) -> Some Compiler_local
              | Sail.Ast_util.Register _ -> Some Compiler_register
              | Sail.Ast_util.Enum _ -> Some Compiler_enum
              | Sail.Ast_util.Unbound _ -> Some Compiler_unbound
            )
        )
    )

let compiler_semantic_token_type_of_lvar = function
  | Compiler_local -> Some "variable"
  | Compiler_register -> Some "property"
  | Compiler_enum -> Some "enumMember"
  | Compiler_unbound -> None

let compiler_semantic_tokens uri text =
  let max_identifiers = 1500 in
  let identifier_count = ref 0 in
  lines_of_text text
  |> List.mapi (fun line_no line ->
      tokens_from line 0
      |> List.filter_map (fun (word, start, stop) ->
          if
            !identifier_count >= max_identifiers || word = "" || List.mem word sail_keywords
            || not (is_ident_char word.[0])
          then None
          else (
            incr identifier_count;
            let position = { line = line_no; character = start } in
            Option.bind (compiler_lvar_kind_at_position uri text position word) (fun kind ->
                Option.map
                  (fun token_type -> add_semantic_token line_no start stop token_type [])
                  (compiler_semantic_token_type_of_lvar kind)
            )
            |> Option.map List.hd
          )
      )
  )
  |> List.concat

let merge_semantic_tokens base overlay =
  let seen = Hashtbl.create 256 in
  let key token = (token.token_line, token.token_start, token.token_length) in
  List.iter (fun token -> Hashtbl.replace seen (key token) ()) overlay;
  overlay @ List.filter (fun token -> not (Hashtbl.mem seen (key token))) base
  |> List.sort (fun a b ->
      match compare a.token_line b.token_line with 0 -> compare a.token_start b.token_start | n -> n
  )

let typed_semantic_tokens_with_workspace uri text =
  merge_semantic_tokens (semantic_tokens_with_workspace uri text) (compiler_semantic_tokens uri text)

let unique_strings strings =
  let seen = Hashtbl.create 16 in
  List.filter
    (fun s ->
      if Hashtbl.mem seen s then false
      else (
        Hashtbl.add seen s ();
        true
      )
    )
    strings

let default_c_output_candidates ?(recursive = true) () =
  let root = root_or_cwd () in
  let base = [Filename.concat root "out.c"; Filename.concat root "out.cpp"] in
  if recursive then base @ collect_files_by_suffix ".c" root @ collect_files_by_suffix ".cpp" root else base

let c_output_candidates () =
  match !configured_c_output with
  | Some path -> [absolutize_against_root path]
  | None -> unique_strings (artifact_c_outputs () @ default_c_output_candidates ~recursive:true ())

let c_map_candidates () =
  let candidates =
    match !configured_c_map with
    | Some path -> [absolutize_against_root path]
    | None ->
        let root = root_or_cwd () in
        artifact_c_maps ()
        @ List.map (fun path -> path ^ ".symbols.json") (artifact_c_outputs ())
        @ List.map (fun path -> path ^ ".symbols.json") (default_c_output_candidates ~recursive:false ())
        @ [
            Filename.concat root "out.c.symbols.json";
            Filename.concat root "out.cpp.symbols.json";
            Filename.concat root "out.symbols.json";
          ]
        @ collect_files_by_suffix ".symbols.json" root
  in
  unique_strings candidates

let docinfo_candidates () =
  let candidates =
    match !configured_docinfo with
    | Some path -> [absolutize_against_root path]
    | None ->
        let root = root_or_cwd () in
        artifact_docinfos ()
        @ [
            Filename.concat root "doc.json";
            Filename.concat root "sail_doc/doc.json";
            Filename.concat root "docs/doc.json";
            Filename.concat root "out.docinfo.json";
          ]
  in
  unique_strings candidates

let has_path_separator path = String.contains path '/' || String.contains path '\\'

let executable_path path =
  if Filename.is_relative path && has_path_separator path then (
    let launch_relative = Filename.concat server_launch_cwd path in
    if Sys.file_exists launch_relative then launch_relative else absolutize_against_root path
  )
  else path

let shell_quote value = "'" ^ String.concat "'\\''" (String.split_on_char '\'' value) ^ "'"

let run_command_capture ?cwd args =
  let command = String.concat " " (List.map shell_quote args) in
  let command =
    match cwd with Some cwd -> "cd " ^ shell_quote cwd ^ " && " ^ command ^ " 2>&1" | None -> command ^ " 2>&1"
  in
  try
    let channel = Unix.open_process_in command in
    let output = read_channel_all channel in
    let status = Unix.close_process_in channel in
    (status, output)
  with Unix.Unix_error (error, _, _) -> (Unix.WEXITED 127, Unix.error_message error)

let run_command_stdout ?cwd args =
  let command = String.concat " " (List.map shell_quote args) in
  let command = match cwd with Some cwd -> "cd " ^ shell_quote cwd ^ " && " ^ command | None -> command in
  try
    let channel = Unix.open_process_in command in
    let output = read_channel_all channel in
    let status = Unix.close_process_in channel in
    (status, output)
  with Unix.Unix_error (error, _, _) -> (Unix.WEXITED 127, Unix.error_message error)

let process_succeeded = function Unix.WEXITED 0 -> true | _ -> false

type compiler_diagnostic = {
  diag_file : string;
  diag_range : range;
  diag_severity : int;
  diag_code : string option;
  diag_message : string;
  diag_origin : string option;
}

let split_once_char ch s =
  match String.index_opt s ch with
  | None -> None
  | Some i -> Some (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))

let parse_line_col s =
  match split_once_char '.' s with
  | Some (line, col) ->
      Option.bind (int_of_string_opt line) (fun line -> Option.map (fun col -> (line, col)) (int_of_string_opt col))
  | None -> None

let parse_location_suffix suffix =
  let parse_end line1 rhs =
    match parse_line_col rhs with
    | Some (line2, col2) -> Some (line2, col2)
    | None -> Option.map (fun col2 -> (line1, col2)) (int_of_string_opt rhs)
  in
  match split_once_char '-' suffix with
  | Some (lhs, rhs) -> (
      match parse_line_col lhs with
      | Some (line1, col1) -> (
          match parse_end line1 rhs with
          | Some (line2, col2) ->
              Some
                {
                  start_pos = { line = max 0 (line1 - 1); character = max 0 (col1 - 1) };
                  end_pos = { line = max 0 (line2 - 1); character = max 0 col2 };
                }
          | None -> None
        )
      | None -> None
    )
  | None -> (
      match parse_line_col suffix with
      | Some (line, col) ->
          Some
            {
              start_pos = { line = max 0 (line - 1); character = max 0 (col - 1) };
              end_pos = { line = max 0 (line - 1); character = max 0 col };
            }
      | None -> None
    )

let strip_location_prefix s =
  let s = String.trim s in
  if starts_with ~prefix:"|" s then String.sub s 1 (String.length s - 1) |> String.trim else s

let heading_contains_warning heading = starts_with ~prefix:"Warning:" heading

let parse_location_line current_heading current_severity line =
  let line = strip_location_prefix line in
  if line = "" then None
  else (
    let line = if line.[String.length line - 1] = ':' then String.sub line 0 (String.length line - 1) else line in
    match String.rindex_opt line ':' with
    | None -> None
    | Some colon -> (
        let prefix = String.sub line 0 colon |> String.trim in
        let suffix = String.sub line (colon + 1) (String.length line - colon - 1) |> String.trim in
        match parse_location_suffix suffix with
        | None -> None
        | Some diag_range ->
            let diag_file, diag_heading, diag_severity =
              if heading_contains_warning prefix then (
                match String.rindex_opt prefix ' ' with
                | Some space ->
                    ( String.sub prefix (space + 1) (String.length prefix - space - 1),
                      String.sub prefix 0 space |> String.trim,
                      2
                    )
                | None -> (prefix, "Warning", 2)
              )
              else (prefix, current_heading, current_severity)
            in
            Some (diag_file, diag_range, diag_severity, diag_heading)
      )
  )

let string_for_all pred s =
  let rec loop i = i >= String.length s || (pred s.[i] && loop (i + 1)) in
  loop 0

let is_source_echo_line line =
  let line = String.trim line in
  let len = String.length line in
  let rec digits i = if i < len && is_digit line.[i] then digits (i + 1) else i in
  let i = digits 0 in
  if i = 0 then false
  else (
    let rec spaces j = if j < len && is_space line.[j] then spaces (j + 1) else j in
    let j = spaces i in
    j < len && line.[j] = '|'
  )

let message_candidate_from_line line =
  let trimmed = String.trim line in
  if trimmed = "" || is_source_echo_line trimmed then None
  else (
    let candidate =
      match String.rindex_opt trimmed '|' with
      | Some bar -> String.sub trimmed (bar + 1) (String.length trimmed - bar - 1) |> String.trim
      | None -> trimmed
    in
    if candidate = "" || string_for_all (function '^' | '-' | '~' | ' ' | '\t' -> true | _ -> false) candidate then None
    else Some candidate
  )

let first_message_after lines index =
  let rec loop remaining i =
    if remaining = 0 then None
    else (
      match List.nth_opt lines i with
      | None -> None
      | Some line -> (
          match message_candidate_from_line line with
          | Some _ as message -> message
          | None -> loop (remaining - 1) (i + 1)
        )
    )
  in
  loop 8 (index + 1)

let lowercase_ascii_contains haystack needle =
  let haystack = String.lowercase_ascii haystack in
  let needle = String.lowercase_ascii needle in
  let haystack_len = String.length haystack in
  let needle_len = String.length needle in
  needle_len = 0
  ||
  let rec loop i = i + needle_len <= haystack_len && (String.sub haystack i needle_len = needle || loop (i + 1)) in
  loop 0

let heading_from_line line =
  let trimmed = String.trim line in
  if trimmed = "" then None
  else if String.get trimmed (String.length trimmed - 1) = ':' then Some trimmed
  else if lowercase_ascii_contains trimmed "error" || heading_contains_warning trimmed then Some trimmed
  else None

let severity_from_heading heading =
  if heading_contains_warning heading || lowercase_ascii_contains heading "warning" then 2 else 1

let diagnostic_code message =
  if lowercase_ascii_contains message "could not infer type" then Some "sail.type.infer"
  else if lowercase_ascii_contains message "type mismatch" then Some "sail.type.mismatch"
  else if lowercase_ascii_contains message "types are not well-formed" then Some "sail.type.wellformed"
  else if lowercase_ascii_contains message "well-formedness check failed" then Some "sail.type.wellformed"
  else if lowercase_ascii_contains message "function does not have a function type" then Some "sail.type.function"
  else if lowercase_ascii_contains message "no default order" then Some "sail.order.default"
  else if lowercase_ascii_contains message "default order has been set" then Some "sail.order.default"
  else if lowercase_ascii_contains message "duplicate binding" then Some "sail.name.duplicateBinding"
  else if lowercase_ascii_contains message "unbound" then Some "sail.name.unbound"
  else if lowercase_ascii_contains message "not in scope" then Some "sail.name.unbound"
  else if lowercase_ascii_contains message "no numeric type named" then Some "sail.name.unbound"
  else if lowercase_ascii_contains message "lex" then Some "sail.lex"
  else if lowercase_ascii_contains message "parse" then Some "sail.parse"
  else if lowercase_ascii_contains message "warning" then Some "sail.warning"
  else Some "sail.error"

let compiler_diagnostics_from_output output =
  let lines = lines_of_text output in
  let rec loop index current_heading current_severity acc =
    match List.nth_opt lines index with
    | None -> List.rev acc
    | Some line -> (
        match parse_location_line current_heading current_severity line with
        | Some (diag_file, diag_range, diag_severity, diag_heading) ->
            let message =
              match first_message_after lines index with
              | Some detail when diag_heading <> "" -> diag_heading ^ "\n" ^ detail
              | Some detail -> detail
              | None -> diag_heading
            in
            loop (index + 1) current_heading current_severity
              ({
                 diag_file;
                 diag_range;
                 diag_severity;
                 diag_code = diagnostic_code message;
                 diag_message = message;
                 diag_origin = Some "text";
               }
              :: acc
              )
        | None -> (
            match heading_from_line line with
            | Some heading -> loop (index + 1) heading (severity_from_heading heading) acc
            | None -> loop (index + 1) current_heading current_severity acc
          )
      )
  in
  loop 0 "Sail diagnostic" 1 []

let path_matches diagnostic_file uri_path =
  let diagnostic_path = absolutize_against_root diagnostic_file in
  diagnostic_path = uri_path || diagnostic_file = uri_path
  ||
  let suffix = "/" ^ diagnostic_file in
  String.length uri_path >= String.length suffix
  && String.sub uri_path (String.length uri_path - String.length suffix) (String.length suffix) = suffix

let diagnostic_json diagnostic =
  let data_fields =
    [
      ("file", `String diagnostic.diag_file);
      ("message", `String diagnostic.diag_message);
      ("origin", match diagnostic.diag_origin with Some origin -> `String origin | None -> `Null);
      ("structured", `Bool (diagnostic.diag_origin = Some "compiler"));
    ]
  in
  let fields =
    [
      ("range", json_range diagnostic.diag_range);
      ("severity", `Int diagnostic.diag_severity);
      ("source", `String "sail");
      ("message", `String diagnostic.diag_message);
      ("data", `Assoc data_fields);
    ]
  in
  let fields = match diagnostic.diag_code with Some code -> ("code", `String code) :: fields | None -> fields in
  `Assoc fields

let publish_diagnostics uri diagnostics =
  notification "textDocument/publishDiagnostics"
    (`Assoc [("uri", `String uri); ("diagnostics", `List (List.map diagnostic_json diagnostics))])

let compiler_check_args path =
  let sail = executable_path !configured_sail_executable in
  match configured_project_for_path path with
  | Some project ->
      let modules = match configured_project_modules () with None -> ["-all_modules"] | Some modules -> modules in
      [sail; "-no_color"; "-just_check"; "-project"; project] @ modules
  | None -> [sail; "-no_color"; "-just_check"; path]

let general_diagnostic message =
  {
    diag_file = "";
    diag_range = { start_pos = { line = 0; character = 0 }; end_pos = { line = 0; character = 1 } };
    diag_severity = 1;
    diag_code = Some "sail.check.failed";
    diag_message = message;
    diag_origin = Some "text";
  }

let diagnostic_file_and_range_of_loc = Source_location.diagnostic_file_and_range_of_loc

let diagnostic_file_and_range_of_position = Source_location.diagnostic_file_and_range_of_position

let structured_diagnostic ?(severity = 1) ?code fallback_path loc message =
  let diag_file, diag_range = diagnostic_file_and_range_of_loc fallback_path loc in
  {
    diag_file;
    diag_range;
    diag_severity = severity;
    diag_code = (match code with Some _ -> code | None -> diagnostic_code message);
    diag_message = message;
    diag_origin = Some "compiler";
  }

let structured_position_diagnostic ?(severity = 1) ?code fallback_path position message =
  let diag_file, diag_range = diagnostic_file_and_range_of_position fallback_path position in
  {
    diag_file;
    diag_range;
    diag_severity = severity;
    diag_code = (match code with Some _ -> code | None -> diagnostic_code message);
    diag_message = message;
    diag_origin = Some "compiler";
  }

let diagnostic_of_reporting_error path = function
  | Sail.Reporting.Err_general (loc, message) -> structured_diagnostic path loc message
  | Sail.Reporting.Err_unreachable (loc, _, _, message) ->
      structured_diagnostic ~code:"sail.internal.unreachable" path loc message
  | Sail.Reporting.Err_todo (loc, message) -> structured_diagnostic ~code:"sail.todo" path loc message
  | Sail.Reporting.Err_syntax (position, message) ->
      structured_position_diagnostic ~code:"sail.parse" path position message
  | Sail.Reporting.Err_syntax_loc (loc, message) -> structured_diagnostic ~code:"sail.parse" path loc message
  | Sail.Reporting.Err_lex (position, message) -> structured_position_diagnostic ~code:"sail.lex" path position message
  | Sail.Reporting.Err_type (loc, hint, message) ->
      let message = match hint with Some hint when hint <> "" -> message ^ "\n" ^ hint | _ -> message in
      structured_diagnostic path loc message

let compiler_structured_diagnostics path =
  try
    ignore (load_compiler_model_uncached path);
    Some []
  with
  | Sail.Reporting.Fatal_error error -> Some [diagnostic_of_reporting_error path error]
  | _ -> None

let ambiguous_project_diagnostic path =
  match (!configured_project, artifact_project (), discover_project_files_for path) with
  | None, None, (_ :: _ :: _ as projects) ->
      Some
        {
          diag_file = path;
          diag_range = { start_pos = { line = 0; character = 0 }; end_pos = { line = 0; character = 1 } };
          diag_severity = 2;
          diag_code = Some "sail.project.ambiguous";
          diag_message =
            "Multiple .sail_project files were found near this file. Use Sail: Choose Project File or set \
             sail.projectFile.\n" ^ String.concat "\n" projects;
          diag_origin = Some "lsp";
        }
  | _ -> None

let run_diagnostics_for_uri uri =
  if !diagnostics_enabled then (
    let path = path_of_uri uri in
    if is_sail_source_path path && Sys.file_exists path then (
      let diagnostics =
        match compiler_structured_diagnostics path with
        | Some (_ :: _ as diagnostics) -> diagnostics
        | _ ->
            let status, output = run_command_capture ~cwd:(root_or_cwd ()) (compiler_check_args path) in
            let diagnostics =
              compiler_diagnostics_from_output output
              |> List.filter (fun diagnostic -> diagnostic.diag_file = "" || path_matches diagnostic.diag_file path)
            in
            if diagnostics = [] && (not (process_succeeded status)) && String.trim output <> "" then
              [general_diagnostic ("Sail check failed without a source location:\n" ^ String.trim output)]
            else diagnostics
      in
      let diagnostics =
        match ambiguous_project_diagnostic path with
        | Some diagnostic -> diagnostic :: diagnostics
        | None -> diagnostics
      in
      publish_diagnostics uri diagnostics
    )
  )

let run_diagnostics_for_open_documents () =
  Hashtbl.fold (fun uri _ uris -> uri :: uris) text_documents [] |> List.iter run_diagnostics_for_uri

let full_document_range text =
  let lines = lines_of_text text in
  let last_line_no = max 0 (List.length lines - 1) in
  let last_line = List.nth lines last_line_no in
  { start_pos = { line = 0; character = 0 }; end_pos = { line = last_line_no; character = String.length last_line } }

let remove_file_if_exists path = try Sys.remove path with Sys_error _ -> ()

let with_formatter_input path text f =
  let temp_path = ref None in
  Fun.protect
    ~finally:(fun () -> Option.iter remove_file_if_exists !temp_path)
    (fun () ->
      let format_path =
        match try Some (read_file path) with Sys_error _ -> None with
        | Some disk_text when disk_text = text -> path
        | _ ->
            let temp = Filename.temp_file "sail-lsp-format-" ".sail" in
            temp_path := Some temp;
            write_file temp text;
            temp
      in
      f format_path
    )

let format_document uri text =
  let path = path_of_uri uri in
  let sail = executable_path !configured_sail_executable in
  with_formatter_input path text (fun format_path ->
      let status, output =
        run_command_stdout ~cwd:(root_or_cwd ()) [sail; "-fmt"; "-fmt_emit"; "stdout"; format_path]
      in
      if process_succeeded status then Ok output
      else Error (if String.trim output = "" then "Sail formatter failed." else String.trim output)
  )

let text_edit_json range new_text = `Assoc [("range", json_range range); ("newText", `String new_text)]

let handle_formatting id params =
  match text_document_uri params with
  | None -> response id (`List [])
  | Some uri -> (
      match document_text uri with
      | None -> response id (`List [])
      | Some text -> (
          match format_document uri text with
          | Ok formatted -> response id (`List [text_edit_json (full_document_range text) formatted])
          | Error message ->
              show_message message;
              response id (`List [])
        )
    )

type c_map_entry = {
  sail_name : string;
  c_name : string;
  c_map_path : string;
  c_file : string option;
  c_range : range option;
  kind : string option;
  generated : bool option;
}

let parse_c_map path =
  try
    let json = Json.from_file path in
    let dir = Filename.dirname path in
    let root_c_file = Option.map (absolutize_against_dir dir) (json_string_member "cFile" json) in
    let parse_entry = function
      | `Assoc _ as entry -> (
          match (json_string_member "sailName" entry, json_string_member "cName" entry) with
          | Some sail_name, Some c_name ->
              let c_file = Option.map (absolutize_against_dir dir) (json_string_member "cFile" entry) in
              Some
                {
                  sail_name;
                  c_name;
                  c_map_path = path;
                  c_file = (match c_file with Some _ -> c_file | None -> root_c_file);
                  c_range = Option.bind (json_member "cRange" entry) parse_json_range;
                  kind = json_string_member "kind" entry;
                  generated = json_bool_member "generated" entry;
                }
          | _ -> None
        )
      | _ -> None
    in
    Some (json_list_member "symbols" json |> Option.value ~default:[] |> List.filter_map parse_entry)
  with Sys_error _ | Yojson.Json_error _ -> None

let find_c_map_entry_by predicate =
  let rec try_maps = function
    | [] -> None
    | path :: rest -> (
        match parse_c_map path with
        | Some entries -> (
            match predicate entries with Some _ as found -> found | None -> try_maps rest
          )
        | None -> try_maps rest
      )
  in
  try_maps (c_map_candidates ())

let find_c_map_entry sail_name =
  let find_in_entries entries =
    match List.find_opt (fun entry -> entry.sail_name = sail_name) entries with
    | Some _ as exact -> exact
    | None ->
        let specialized_prefixes = [sail_name ^ "<"; sail_name ^ "#"] in
        List.find_opt
          (fun entry -> List.exists (fun prefix -> starts_with ~prefix entry.sail_name) specialized_prefixes)
          entries
  in
  find_c_map_entry_by find_in_entries

let find_c_map_entry_by_c_name c_name =
  find_c_map_entry_by (fun entries -> List.find_opt (fun entry -> entry.c_name = c_name) entries)

let is_c_ident_char = function 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' -> true | _ -> false

let identifier_at line name start =
  let name_len = String.length name in
  start + name_len <= String.length line
  && String.sub line start name_len = name
  && (start = 0 || not (is_c_ident_char line.[start - 1]))
  && (start + name_len = String.length line || not (is_c_ident_char line.[start + name_len]))

let find_identifier_in_line line name =
  let name_len = String.length name in
  let rec search i =
    if i + name_len > String.length line then None else if identifier_at line name i then Some i else search (i + 1)
  in
  search 0

let find_c_location_in_files files c_name =
  let rec try_files = function
    | [] -> None
    | path :: paths -> (
        try
          let lines = read_file path |> lines_of_text in
          let rec scan line_no = function
            | [] -> try_files paths
            | line :: rest -> (
                match find_identifier_in_line line c_name with
                | Some character ->
                    let range =
                      {
                        start_pos = { line = line_no; character };
                        end_pos = { line = line_no; character = character + String.length c_name };
                      }
                    in
                    Some (uri_of_path path, range)
                | None -> scan (line_no + 1) rest
              )
          in
          scan 0 lines
        with Sys_error _ -> try_files paths
      )
  in
  try_files files

let c_files_for_entry entry =
  match entry.c_file with
  | Some path -> [path]
  | None -> (
      match artifact_c_output_for_map entry.c_map_path with Some path -> [path] | None -> c_output_candidates ()
    )

let c_location_of_entry entry =
  match (entry.c_file, entry.c_range) with Some path, Some range -> Some (uri_of_path path, range) | _ -> None

let find_c_location_for_entry entry =
  match c_location_of_entry entry with
  | Some _ as location -> location
  | None -> find_c_location_in_files (c_files_for_entry entry) entry.c_name

let find_c_location c_name =
  match find_c_map_entry_by_c_name c_name with
  | Some entry -> find_c_location_for_entry entry
  | None -> find_c_location_in_files (c_output_candidates ()) c_name

type string_literal = { value : string; value_start : int; value_stop : int; literal_start : int; literal_stop : int }

let string_literals_in_text text =
  let len = String.length text in
  let rec scan i acc =
    if i >= len then List.rev acc
    else if text.[i] <> '"' then scan (i + 1) acc
    else (
      let value_start = i + 1 in
      let buf = Buffer.create 16 in
      let rec take j escaped =
        if j >= len then List.rev acc
        else if escaped then (
          Buffer.add_char buf text.[j];
          take (j + 1) false
        )
        else (
          match text.[j] with
          | '\\' -> take (j + 1) true
          | '"' ->
              let literal =
                { value = Buffer.contents buf; value_start; value_stop = j; literal_start = i; literal_stop = j + 1 }
              in
              scan (j + 1) (literal :: acc)
          | c ->
              Buffer.add_char buf c;
              take (j + 1) false
        )
      in
      take value_start false
    )
  in
  scan 0 []

let string_literal_at_offset text offset =
  let len = String.length text in
  let rec scan i =
    if i >= len then None
    else if text.[i] <> '"' then scan (i + 1)
    else (
      let value_start = i + 1 in
      let buf = Buffer.create 16 in
      let rec take j escaped =
        if j >= len then None
        else if escaped then (
          Buffer.add_char buf text.[j];
          take (j + 1) false
        )
        else (
          match text.[j] with
          | '\\' -> take (j + 1) true
          | '"' ->
              let literal =
                { value = Buffer.contents buf; value_start; value_stop = j; literal_start = i; literal_stop = j + 1 }
              in
              if offset >= value_start && offset <= j then Some literal else scan (j + 1)
          | c ->
              Buffer.add_char buf c;
              take (j + 1) false
        )
      in
      take value_start false
    )
  in
  scan 0

let is_c_annotation_value text literal =
  let rec skip_spaces_left i = if i >= 0 && is_space text.[i] then skip_spaces_left (i - 1) else i in
  let colon = skip_spaces_left (literal.literal_start - 1) in
  if colon < 0 || text.[colon] <> ':' then false
  else (
    let key_stop = skip_spaces_left (colon - 1) + 1 in
    let rec key_start i = if i >= 0 && is_ident_char text.[i] then key_start (i - 1) else i + 1 in
    let key_start = key_start (key_stop - 1) in
    key_start < key_stop && String.sub text key_start (key_stop - key_start) = "c"
  )

let c_annotation_at_position text position =
  let offset = offset_of_position text position in
  match string_literal_at_offset text offset with
  | Some literal when is_c_annotation_value text literal ->
      Some
        ( literal.value,
          {
            start_pos = position_of_offset text literal.value_start;
            end_pos = position_of_offset text literal.value_stop;
          }
        )
  | _ -> None

type generated_c_target = {
  sail_name : string option;
  c_name : string;
  c_files : string list;
  c_location : (string * range) option;
  kind : string option;
  generated : bool option;
  source : string;
  fallback_reason : string option;
}

let generated_c_target_at_position text position =
  match c_annotation_at_position text position with
  | Some (c_name, _) -> (
      match find_c_map_entry_by_c_name c_name with
      | Some entry ->
          Some
            {
              sail_name = Some entry.sail_name;
              c_name = entry.c_name;
              c_files = c_files_for_entry entry;
              c_location = c_location_of_entry entry;
              kind = entry.kind;
              generated = entry.generated;
              source = "sidecar";
              fallback_reason = None;
            }
      | None ->
          Some
            {
              sail_name = None;
              c_name;
              c_files = c_output_candidates ();
              c_location = None;
              kind = Some "extern";
              generated = Some false;
              source = "annotation";
              fallback_reason = None;
            }
    )
  | None -> (
      match word_at_position text position with
      | None -> None
      | Some sail_name -> (
          match find_c_map_entry sail_name with
          | Some entry ->
              Some
                {
                  sail_name = Some entry.sail_name;
                  c_name = entry.c_name;
                  c_files = c_files_for_entry entry;
                  c_location = c_location_of_entry entry;
                  kind = entry.kind;
                  generated = entry.generated;
                  source = "sidecar";
                  fallback_reason = None;
                }
          | None ->
              Some
                {
                  sail_name = Some sail_name;
                  c_name = Libsail.Util.zencode_string sail_name;
                  c_files = c_output_candidates ();
                  c_location = None;
                  kind = None;
                  generated = None;
                  source = "zencodeFallback";
                  fallback_reason = Some "No generated-C sidecar entry was found for this Sail identifier.";
                }
        )
    )

let generated_c_location target =
  match target.c_location with
  | Some _ as location -> location
  | None -> find_c_location_in_files target.c_files target.c_name

type doc_location = { doc_uri : string; doc_range : range }

type doc_entry = {
  doc_name : string;
  doc_kind : string;
  doc_path : string;
  doc_url : string option;
  doc_json : Json.t;
  doc_markdown : string;
  doc_location : doc_location option;
}

let json_field fields key = List.assoc_opt key fields

let rec first_string_member key = function
  | `Assoc fields -> (
      match Option.bind (json_field fields key) json_string_value with
      | Some _ as found -> found
      | None -> fields |> List.find_map (fun (_, value) -> first_string_member key value)
    )
  | `List values -> List.find_map (first_string_member key) values
  | _ -> None

let rec first_location_json = function
  | `Assoc fields as json -> (
      match (json_field fields "file", json_field fields "loc") with
      | Some (`String _), Some (`List _) -> Some json
      | _ -> fields |> List.find_map (fun (_, value) -> first_location_json value)
    )
  | `List values -> List.find_map first_location_json values
  | _ -> None

let doc_location_of_json docinfo_path = function
  | `Assoc fields -> (
      match (json_field fields "file", json_field fields "loc") with
      | Some (`String file), Some (`List [`Int line1; `Int bol1; `Int char1; `Int line2; `Int bol2; `Int char2]) ->
          let resolve_file file =
            if Filename.is_relative file then (
              let root = root_or_cwd () in
              let candidates =
                [
                  Filename.concat root file;
                  Filename.concat (Filename.dirname docinfo_path) file;
                  Filename.concat (Sys.getcwd ()) file;
                ]
              in
              List.find_opt Sys.file_exists candidates |> Option.value ~default:(Filename.concat root file)
            )
            else file
          in
          let range =
            {
              start_pos = { line = max 0 (line1 - 1); character = max 0 (char1 - bol1) };
              end_pos = { line = max 0 (line2 - 1); character = max 0 (char2 - bol2) };
            }
          in
          Some { doc_uri = uri_of_path (resolve_file file); doc_range = range }
      | _ -> None
    )
  | _ -> None

let truncate_for_hover s =
  let max_len = 1400 in
  if String.length s <= max_len then s else String.sub s 0 max_len ^ "\n..."

let markdown_code_block language contents = "```" ^ language ^ "\n" ^ truncate_for_hover contents ^ "\n```"

let raw_or_contents = function `String s -> Some s | json -> first_string_member "contents" json

let first_string_member_any keys json = List.find_map (fun key -> first_string_member key json) keys

let doc_source_for_kind kind json =
  let primary_keys =
    match kind with
    | "val" | "register" -> ["type"; "source"]
    | "let" -> ["exp"; "source"]
    | "span" -> ["span"]
    | _ -> ["source"; "type"; "body"]
  in
  List.find_map
    (fun key -> raw_or_contents (match json_member key json with Some value -> value | None -> `Null))
    primary_keys
  |> function
  | Some _ as found -> found
  | None -> raw_or_contents json

let markdown_of_doc_entry name kind json =
  let title = Printf.sprintf "**Sail %s** `%s`" kind name in
  let comment = first_string_member "comment" json in
  let source = doc_source_for_kind kind json in
  let doc_url = first_string_member_any ["docUrl"; "docURL"; "url"; "href"] json in
  String.concat "\n\n"
    (List.filter
       (fun s -> s <> "")
       [
         title;
         (match comment with Some text -> String.trim text | None -> "");
         (match source with Some text -> markdown_code_block "sail" text | None -> "");
         (match doc_url with Some url -> Printf.sprintf "[Generated documentation](%s)" url | None -> "");
       ]
    )

let load_docinfo () =
  let rec try_paths = function
    | [] -> None
    | path :: rest -> (
        try Some (path, Json.from_file path) with Sys_error _ | Yojson.Json_error _ -> try_paths rest
      )
  in
  try_paths (docinfo_candidates ())

let doc_entry_from_json docinfo_path name kind json =
  let location = Option.bind (first_location_json json) (doc_location_of_json docinfo_path) in
  let doc_url = first_string_member_any ["docUrl"; "docURL"; "url"; "href"] json in
  {
    doc_name = name;
    doc_kind = kind;
    doc_path = docinfo_path;
    doc_url;
    doc_json = json;
    doc_markdown = markdown_of_doc_entry name kind json;
    doc_location = location;
  }

let clean_doc_comment_line line =
  let line = String.trim line in
  let line =
    if starts_with ~prefix:"///" line then String.sub line 3 (String.length line - 3)
    else if starts_with ~prefix:"//" line then String.sub line 2 (String.length line - 2)
    else if starts_with ~prefix:"/*" line then String.sub line 2 (String.length line - 2)
    else line
  in
  let line = String.trim line in
  let line = if starts_with ~prefix:"*" line then String.sub line 1 (String.length line - 1) |> String.trim else line in
  let line = if ends_with ~suffix:"*/" line then String.sub line 0 (String.length line - 2) |> String.trim else line in
  line

let source_doc_comment_for_symbol text symbol =
  let lines = lines_of_text text in
  let rec collect_line_comments i acc =
    if i < 0 then acc
    else (
      match List.nth_opt lines i with
      | Some line when starts_with ~prefix:"//" (String.trim line) ->
          collect_line_comments (i - 1) (clean_doc_comment_line line :: acc)
      | _ -> acc
    )
  in
  let rec collect_block_comment i acc =
    if i < 0 then None
    else (
      match List.nth_opt lines i with
      | None -> None
      | Some line ->
          let cleaned = clean_doc_comment_line line in
          if starts_with ~prefix:"/*" (String.trim line) then Some (cleaned :: acc)
          else collect_block_comment (i - 1) (cleaned :: acc)
    )
  in
  let previous_line = symbol.range.start_pos.line - 1 in
  match List.nth_opt lines previous_line with
  | Some line when starts_with ~prefix:"//" (String.trim line) ->
      let comment = collect_line_comments previous_line [] |> List.filter (fun line -> line <> "") in
      if comment = [] then None else Some (String.concat "\n" comment)
  | Some line when ends_with ~suffix:"*/" (String.trim line) ->
      collect_block_comment previous_line []
      |> Option.map (fun lines -> String.concat "\n" (List.filter (fun line -> line <> "") lines))
  | _ -> None

let source_doc_entry_for_name uri text name =
  workspace_documents ~current_uri:uri ~current_text:text ()
  |> List.find_map (fun doc ->
      document_symbols doc.doc_uri doc.doc_text
      |> List.find_map (fun symbol ->
          if symbol.name = name then
            source_doc_comment_for_symbol doc.doc_text symbol
            |> Option.map (fun comment ->
                let fields =
                  ("comment", `String comment)
                  ::
                  ( match source_type_for_symbol doc.doc_text symbol with
                  | Some ty -> [("type", `String ty)]
                  | None -> []
                  )
                in
                let json = `Assoc fields in
                {
                  doc_name = name;
                  doc_kind = symbol.detail;
                  doc_path = doc.doc_path;
                  doc_url = None;
                  doc_json = json;
                  doc_markdown = markdown_of_doc_entry name symbol.detail json;
                  doc_location = Some { doc_uri = doc.doc_uri; doc_range = symbol.selection_range };
                }
            )
          else None
      )
  )

let find_docinfo_entry name =
  let find_in_section docinfo_path root section kind =
    match json_member section root with
    | Some (`Assoc entries) -> Option.map (doc_entry_from_json docinfo_path name kind) (List.assoc_opt name entries)
    | _ -> None
  in
  match load_docinfo () with
  | None -> None
  | Some (path, root) ->
      [
        ("functions", "function");
        ("mappings", "mapping");
        ("vals", "val");
        ("types", "type");
        ("registers", "register");
        ("lets", "let");
        ("anchors", "anchor");
        ("spans", "span");
      ]
      |> List.find_map (fun (section, kind) -> find_in_section path root section kind)

let find_documentation_entry uri text name =
  match find_docinfo_entry name with Some _ as entry -> entry | None -> source_doc_entry_for_name uri text name

let doc_location_json = function None -> `Null | Some location -> location_json location.doc_uri location.doc_range

let doc_entry_type entry = first_string_member "type" entry.doc_json

let doc_entry_type_json entry = match doc_entry_type entry with Some ty -> `String ty | None -> `Null

let doc_entry_json entry =
  `Assoc
    [
      ("name", `String entry.doc_name);
      ("kind", `String entry.doc_kind);
      ("docinfo", `String entry.doc_path);
      ("type", doc_entry_type_json entry);
      ("url", match entry.doc_url with Some url -> `String url | None -> `Null);
      ("markdown", `String entry.doc_markdown);
      ("location", doc_location_json entry.doc_location);
      ("raw", entry.doc_json);
    ]

let source_graph_cache_key current_uri =
  String.concat "\000"
    [
      root_or_cwd ();
      Option.value ~default:"workspace" current_uri;
      Option.value ~default:"" !configured_project;
      String.concat "," !configured_modules;
      string_of_bool !configured_modules_explicit;
      string_of_bool !configured_all_modules;
      string_of_bool !configured_all_modules_explicit;
      Option.value ~default:"" !configured_c_output;
      Option.value ~default:"" !configured_c_map;
      Option.value ~default:"" !configured_docinfo;
      Option.value ~default:"" !configured_artifact_index;
      artifact_index_cache_fragment ();
    ]

let source_graph_type_for_symbol (doc : workspace_document) symbol =
  match compiler_type_entry_for_name doc.doc_uri doc.doc_text symbol.name with
  | Some entry -> (Some entry.compiler_kind, Some entry.compiler_type, Some "compiler")
  | None -> (
      match source_type_for_symbol doc.doc_text symbol with
      | Some source_type -> (None, Some source_type, Some "source")
      | None -> (
          match source_type_entry_for_name doc.doc_uri doc.doc_text symbol.name with
          | Some entry -> (None, Some entry.source_type, Some "source")
          | None -> (None, None, None)
        )
    )

let source_graph_doc_url name = match find_docinfo_entry name with Some entry -> entry.doc_url | None -> None

let source_graph_c_mapping doc_text symbol =
  match generated_c_target_at_position doc_text symbol.selection_range.start_pos with
  | Some target when target.source <> "zencodeFallback" ->
      Some (target.c_name, target.source, generated_c_location target)
  | _ -> None

let source_graph_origin compiler_kind type_source doc_url c_mapping =
  match (compiler_kind, type_source, doc_url, c_mapping) with
  | Some _, _, _, _ | _, Some "compiler", _, _ -> "compiler"
  | _, _, Some _, _ -> "docinfo"
  | _, _, _, Some _ -> "generated"
  | _ -> "source"

let source_graph_reference_index docs =
  let table = Hashtbl.create 512 in
  let add name reference =
    let references = Hashtbl.find_opt table name |> Option.value ~default:[] in
    Hashtbl.replace table name (reference :: references)
  in
  docs
  |> List.iter (fun doc -> identifier_ranges_in_document doc |> List.iter (fun (name, reference) -> add name reference));
  table

let source_graph_references_for index name = Hashtbl.find_opt index name |> Option.value ~default:[] |> List.rev

let source_graph_entry_for_symbol reference_index (doc : workspace_document) symbol =
  let compiler_kind, graph_type, graph_type_source = source_graph_type_for_symbol doc symbol in
  let doc_url = source_graph_doc_url symbol.name in
  let c_mapping = source_graph_c_mapping doc.doc_text symbol in
  let graph_c_name, graph_c_source, graph_c_location =
    match c_mapping with
    | Some (c_name, source, location) -> (Some c_name, Some source, location)
    | None -> (None, None, None)
  in
  {
    graph_name = symbol.name;
    graph_kind = symbol.detail;
    graph_uri = symbol.uri;
    graph_range = symbol.range;
    graph_selection_range = symbol.selection_range;
    graph_origin = source_graph_origin compiler_kind graph_type_source doc_url c_mapping;
    graph_compiler_kind = compiler_kind;
    graph_type;
    graph_type_source;
    graph_doc_url = doc_url;
    graph_c_name;
    graph_c_source;
    graph_c_location;
    graph_references = source_graph_references_for reference_index symbol.name;
  }

let build_source_graph ?current_uri ?current_text () =
  let docs = workspace_documents ?current_uri ?current_text () in
  let reference_index = source_graph_reference_index docs in
  docs
  |> List.concat_map (fun doc ->
      document_symbols doc.doc_uri doc.doc_text |> List.map (source_graph_entry_for_symbol reference_index doc)
  )

let source_graph ?current_uri ?current_text () =
  let key = source_graph_cache_key current_uri in
  match Hashtbl.find_opt source_graph_cache key with
  | Some entries -> entries
  | None ->
      let entries = build_source_graph ?current_uri ?current_text () in
      Hashtbl.replace source_graph_cache key entries;
      entries

let source_graph_preference entry = symbol_preference entry.graph_kind

let source_graph_find_symbol uri text name =
  source_graph ~current_uri:uri ~current_text:text ()
  |> List.filter (fun entry -> entry.graph_name = name)
  |> List.sort (fun a b -> compare (source_graph_preference a) (source_graph_preference b))
  |> List.find_opt (fun _ -> true)

let source_graph_symbol_location uri text name =
  source_graph_find_symbol uri text name |> Option.map (fun entry -> (entry.graph_uri, entry.graph_selection_range))

let source_graph_reference_ranges uri text name =
  source_graph_find_symbol uri text name |> Option.map (fun entry -> entry.graph_references)

let semantic_type_of_graph_entry entry =
  match entry.graph_compiler_kind with
  | Some "register" -> "property"
  | Some "enum member" -> "enumMember"
  | Some "constructor" -> "function"
  | Some "mapping" -> "function"
  | Some "function" -> "function"
  | _ -> semantic_type_of_symbol_detail entry.graph_kind

let semantic_source_graph_symbol_table uri text =
  let table = Hashtbl.create 256 in
  source_graph ~current_uri:uri ~current_text:text ()
  |> List.iter (fun entry -> Hashtbl.replace table entry.graph_name (semantic_type_of_graph_entry entry));
  table

let graph_semantic_tokens_with_workspace uri text =
  let base =
    lines_of_text text
    |> List.mapi (semantic_tokens_for_line (semantic_source_graph_symbol_table uri text))
    |> List.concat |> List.rev
  in
  merge_semantic_tokens
    (List.sort
       (fun a b -> match compare a.token_line b.token_line with 0 -> compare a.token_start b.token_start | n -> n)
       base
    )
    (compiler_semantic_tokens uri text)

let nullable_string_json = function Some value -> `String value | None -> `Null

let nullable_location_json = function Some (uri, range) -> location_json uri range | None -> `Null

let located_range_json reference = location_json reference.loc_uri reference.loc_range

let source_graph_entry_json entry =
  `Assoc
    [
      ("name", `String entry.graph_name);
      ("kind", `String entry.graph_kind);
      ("origin", `String entry.graph_origin);
      ("compilerKind", nullable_string_json entry.graph_compiler_kind);
      ("type", nullable_string_json entry.graph_type);
      ("typeSource", nullable_string_json entry.graph_type_source);
      ("docUrl", nullable_string_json entry.graph_doc_url);
      ("cName", nullable_string_json entry.graph_c_name);
      ("cSource", nullable_string_json entry.graph_c_source);
      ("cLocation", nullable_location_json entry.graph_c_location);
      ("referenceCount", `Int (List.length entry.graph_references));
      ("references", `List (List.map located_range_json entry.graph_references));
      ("location", location_json entry.graph_uri entry.graph_selection_range);
    ]

let handle_source_map id params =
  let current_uri = text_document_uri params in
  let current_text = Option.bind current_uri document_text in
  let entries = source_graph ?current_uri ?current_text () in
  response id (`List (List.map source_graph_entry_json entries))

let source_graph_symbol_information_json entry =
  `Assoc
    [
      ("name", `String entry.graph_name);
      ("kind", `Int (keyword_symbol_kind entry.graph_kind));
      ("location", location_json entry.graph_uri entry.graph_selection_range);
      ("containerName", `String (entry.graph_kind ^ " / " ^ entry.graph_origin));
    ]

let handle_workspace_symbol id params =
  let query = json_string_member "query" params |> Option.value ~default:"" in
  let symbols =
    source_graph ()
    |> List.filter (fun entry -> lowercase_contains entry.graph_name query || lowercase_contains entry.graph_kind query)
    |> List.map source_graph_symbol_information_json
  in
  response id (`List symbols)

let completion_kind_of_graph_entry entry =
  match (entry.graph_compiler_kind, entry.graph_kind) with
  | Some "register", _ -> 10
  | Some "enum member", _ -> 20
  | Some "constructor", _ -> 4
  | Some ("mapping" | "function"), _ -> 3
  | _, ("function" | "mapping" | "operator") -> 3
  | _, ("type" | "struct" | "union" | "bitfield") -> 22
  | _, "enum" -> 13
  | _, "register" -> 10
  | _, "constant" -> 21
  | _, ("val" | "let") -> 12
  | _ -> 6

let completion_prefix text position =
  let offset = offset_of_position text position in
  let rec left i = if i > 0 && is_ident_char text.[i - 1] then left (i - 1) else i in
  let start = left offset in
  String.sub text start (offset - start)

let completion_documentation_json entry =
  match
    Option.bind (document_text entry.graph_uri) (fun text ->
        find_documentation_entry entry.graph_uri text entry.graph_name
    )
  with
  | Some doc -> Some (`Assoc [("kind", `String "markdown"); ("value", `String doc.doc_markdown)])
  | None -> None

let completion_item_json entry =
  let detail =
    match entry.graph_type with
    | Some ty -> Printf.sprintf "%s : %s" entry.graph_kind ty
    | None -> Printf.sprintf "%s / %s" entry.graph_kind entry.graph_origin
  in
  let fields =
    [
      ("label", `String entry.graph_name);
      ("kind", `Int (completion_kind_of_graph_entry entry));
      ("detail", `String detail);
      ("sortText", `String (Printf.sprintf "%02d_%s" (source_graph_preference entry) entry.graph_name));
    ]
  in
  let fields =
    match entry.graph_c_name with
    | Some c_name -> ("data", `Assoc [("cName", `String c_name)]) :: fields
    | None -> fields
  in
  let fields =
    match completion_documentation_json entry with
    | Some documentation -> ("documentation", documentation) :: fields
    | None -> fields
  in
  `Assoc fields

let completion_keyword_item_json keyword =
  `Assoc
    [
      ("label", `String keyword);
      ("kind", `Int 14);
      ("detail", `String "Sail keyword");
      ("sortText", `String ("90_" ^ keyword));
    ]

let completion_local_item_json name =
  `Assoc
    [
      ("label", `String name);
      ("kind", `Int 6);
      ("detail", `String "local let");
      ("sortText", `String ("00_local_" ^ name));
    ]

let completion_pattern_item_json name =
  `Assoc
    [
      ("label", `String name);
      ("kind", `Int 6);
      ("detail", `String "pattern binder");
      ("sortText", `String ("00_pattern_" ^ name));
    ]

let completion_mapping_item_json name =
  `Assoc
    [
      ("label", `String name);
      ("kind", `Int 6);
      ("detail", `String "mapping binder");
      ("sortText", `String ("00_mapping_" ^ name));
    ]

let completion_loop_item_json name =
  `Assoc
    [
      ("label", `String name);
      ("kind", `Int 6);
      ("detail", `String "loop binder");
      ("sortText", `String ("00_loop_" ^ name));
    ]

let completion_parameter_item_json name =
  `Assoc
    [
      ("label", `String name);
      ("kind", `Int 6);
      ("detail", `String "parameter");
      ("sortText", `String ("00_param_" ^ name));
    ]

let completion_source_item_json ~label ~kind ~detail ~sort_group =
  `Assoc
    [
      ("label", `String label);
      ("kind", `Int kind);
      ("detail", `String detail);
      ("sortText", `String (Printf.sprintf "%02d_%s" sort_group label));
    ]

let last_index_of_char ch s =
  let rec loop i = if i < 0 then None else if s.[i] = ch then Some i else loop (i - 1) in
  loop (String.length s - 1)

let last_index_of_any chars s =
  let rec loop i = if i < 0 then None else if List.mem s.[i] chars then Some (i, s.[i]) else loop (i - 1) in
  loop (String.length s - 1)

let last_substring_index ~needle s =
  let needle_len = String.length needle in
  let s_len = String.length s in
  if needle_len = 0 || needle_len > s_len then None
  else (
    let rec loop last i =
      if i + needle_len > s_len then last
      else (
        let last = if String.sub s i needle_len = needle then Some i else last in
        loop last (i + 1)
      )
    in
    loop None 0
  )

let completion_include_context text position =
  match line_at text position.line with
  | None -> None
  | Some line -> (
      let cursor = min position.character (String.length line) in
      let before = String.sub line 0 cursor in
      match last_substring_index ~needle:"$include" (String.lowercase_ascii before) with
      | None -> None
      | Some include_index -> (
          match last_index_of_any ['<'; '"'] before with
          | Some (delimiter_index, delimiter) when delimiter_index > include_index ->
              let prefix = String.sub before (delimiter_index + 1) (cursor - delimiter_index - 1) in
              let closing = if delimiter = '<' then '>' else '"' in
              if String.contains prefix closing then None
              else
                Some
                  (prefix, { start_pos = { line = position.line; character = delimiter_index + 1 }; end_pos = position })
          | _ -> None
        )
    )

let completion_include_item_json range ~label ~kind ~detail =
  `Assoc
    [
      ("label", `String label);
      ("kind", `Int kind);
      ("detail", `String detail);
      ("sortText", `String ("00_include_" ^ label));
      ("textEdit", text_edit_json range label);
    ]

let include_search_roots uri =
  let current_dir = Filename.dirname (path_of_uri uri) in
  unique_strings [current_dir; root_or_cwd (); Filename.concat (compiler_default_sail_dir ()) "lib"]
  |> List.filter (fun path -> try Sys.file_exists path && Sys.is_directory path with Sys_error _ -> false)

let split_include_prefix prefix =
  match last_index_of_char '/' prefix with
  | None -> ("", prefix)
  | Some slash ->
      let dir_prefix = String.sub prefix 0 (slash + 1) in
      let base_prefix = String.sub prefix (slash + 1) (String.length prefix - slash - 1) in
      (dir_prefix, base_prefix)

let include_dir_path root dir_prefix =
  if dir_prefix = "" then Some root
  else if Filename.is_relative dir_prefix then
    Some (Filename.concat root (String.sub dir_prefix 0 (String.length dir_prefix - 1)))
  else None

let include_label dir_prefix name = if dir_prefix = "" then name else dir_prefix ^ name

let include_completion_items_from_root root dir_prefix base_prefix range =
  match include_dir_path root dir_prefix with
  | None -> []
  | Some dir ->
      let entries = try Sys.readdir dir |> Array.to_list with Sys_error _ -> [] in
      entries |> List.sort String.compare
      |> List.filter_map (fun name ->
          let path = Filename.concat dir name in
          try
            if Sys.is_directory path then
              if ignored_workspace_dir name || not (lowercase_starts_with name base_prefix) then None
              else (
                let label = include_label dir_prefix name ^ "/" in
                Some (completion_include_item_json range ~label ~kind:19 ~detail:"Sail include directory")
              )
            else if is_sail_source_path name && lowercase_starts_with name base_prefix then (
              let label = include_label dir_prefix name in
              Some (completion_include_item_json range ~label ~kind:17 ~detail:"Sail include file")
            )
            else None
          with Sys_error _ -> None
      )

let include_completion_item_label = function
  | `Assoc fields -> (
      match List.assoc_opt "label" fields with Some (`String label) -> Some label | _ -> None
    )
  | _ -> None

let unique_include_completion_items items =
  let seen = Hashtbl.create 32 in
  List.filter
    (fun item ->
      match include_completion_item_label item with
      | None -> true
      | Some label ->
          if Hashtbl.mem seen label then false
          else (
            Hashtbl.add seen label ();
            true
          )
    )
    items

let include_completion_items uri prefix range =
  if (not (Filename.is_relative prefix)) || String.contains prefix '\\' then []
  else (
    let dir_prefix, base_prefix = split_include_prefix prefix in
    include_search_roots uri
    |> List.concat_map (fun root -> include_completion_items_from_root root dir_prefix base_prefix range)
    |> unique_include_completion_items
  )

let completion_scope_start_line text position =
  let rec loop line_no =
    if line_no <= 0 then 0
    else (
      match line_at text line_no with
      | Some line when String.trim line <> "" && not (is_space line.[0]) -> line_no
      | _ -> loop (line_no - 1)
    )
  in
  loop position.line

let drop_leading_decl_modifiers tokens =
  let rec loop = function ("private", _, _) :: rest | ("default", _, _) :: rest -> loop rest | tokens -> tokens in
  loop tokens

let token_texts tokens = List.map (fun (token, _, _) -> token) tokens

let is_completion_binder token =
  token <> "" && token <> "_"
  && token.[0] <> '\''
  && (not (is_digit token.[0]))
  && (is_ident_char token.[0] || token.[0] = '_')
  && not (List.mem token sail_keywords)

let is_uppercase_initial token = token <> "" && match token.[0] with 'A' .. 'Z' -> true | _ -> false

let is_pattern_binder token = is_completion_binder token && not (is_uppercase_initial token)

let next_nonspace_char line start stop =
  let rec loop i = if i >= stop then None else if is_space line.[i] then loop (i + 1) else Some line.[i] in
  loop start

let previous_nonspace_char text start =
  let rec loop i = if i < 0 then None else if is_space text.[i] then loop (i - 1) else Some text.[i] in
  loop (start - 1)

let as_can_introduce_alias text token_start skip =
  Option.is_some skip
  ||
  match previous_nonspace_char text token_start with
  | Some (')' | ']' | '}' | '_') -> true
  | Some c when is_digit c -> true
  | _ -> false

let local_let_pattern_end line start =
  let len = String.length line in
  let rec loop i depth =
    if i >= len then len
    else (
      match line.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1)
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1))
      | ('=' | ':') when depth = 0 -> i
      | _ -> loop (i + 1) depth
    )
  in
  loop start 0

let pattern_binder_tokens_from_slice line start stop =
  let stop = min stop (String.length line) in
  let rec take_ident j = if j < stop && is_ident_char line.[j] then take_ident (j + 1) else j in
  let annotation_skip_next_depth depth = function Some skip_depth when depth < skip_depth -> None | skip -> skip in
  let alias_next_depth depth = function
    | Some alias_depth when depth < alias_depth -> None
    | alias_next -> alias_next
  in
  let rec loop i depth skip alias_next acc =
    let skip = annotation_skip_next_depth depth skip in
    let alias_next = alias_next_depth depth alias_next in
    if i >= stop then List.rev acc
    else (
      match line.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1) skip alias_next acc
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1)) skip alias_next acc
      | ',' ->
          let skip = match skip with Some skip_depth when depth <= skip_depth -> None | _ -> skip in
          let alias_next =
            match alias_next with Some alias_depth when depth <= alias_depth -> None | _ -> alias_next
          in
          loop (i + 1) depth skip alias_next acc
      | ':' when i + 1 < stop && line.[i + 1] = ':' -> loop (i + 2) depth skip alias_next acc
      | ':' -> loop (i + 1) depth (Some depth) None acc
      | c when is_ident_char c ->
          let j = take_ident (i + 1) in
          let token = String.sub line i (j - i) in
          let next_char = next_nonspace_char line j stop in
          let starts_type_or_constructor =
            match next_char with Some ('(' | '{') -> true | Some '[' -> not (is_pattern_binder token) | _ -> false
          in
          let starts_field_label = match next_char with Some '=' -> true | _ -> false in
          let is_pending_alias =
            match alias_next with Some alias_depth when alias_depth = depth -> true | _ -> false
          in
          let acc =
            if
              Option.is_none skip
              && ((not is_pending_alias) || is_pattern_binder token)
              && is_pattern_binder token && (not starts_type_or_constructor) && not starts_field_label
            then (token, i, j) :: acc
            else acc
          in
          let skip, alias_next =
            if token = "as" then if as_can_introduce_alias line i skip then (None, Some depth) else (Some depth, None)
            else if is_pending_alias then (
              let skip = if starts_type_or_constructor || not (is_pattern_binder token) then Some depth else skip in
              (skip, None)
            )
            else (skip, alias_next)
          in
          loop j depth skip alias_next acc
      | _ -> loop (i + 1) depth skip alias_next acc
    )
  in
  loop start 0 None None []

let read_token_from_text text start stop =
  let stop = min stop (String.length text) in
  let rec skip i = if i < stop && is_space text.[i] then skip (i + 1) else i in
  let i = skip start in
  if i >= stop then None
  else (
    let is_token_char = if is_symbolic_char text.[i] then is_symbolic_char else is_ident_char in
    let rec take j = if j < stop && is_token_char text.[j] then take (j + 1) else j in
    let j = take i in
    if i = j then None else Some (String.sub text i (j - i), i, j)
  )

let text_has_ident_boundary text i = i < 0 || i >= String.length text || not (is_ident_char text.[i])

let text_starts_with_keyword text i keyword =
  let keyword_len = String.length keyword in
  i >= 0
  && i + keyword_len <= String.length text
  && String.sub text i keyword_len = keyword
  && text_has_ident_boundary text (i - 1)
  && text_has_ident_boundary text (i + keyword_len)

let next_nonspace_char_text text start stop =
  let stop = min stop (String.length text) in
  let rec loop i = if i >= stop then None else if is_space text.[i] then loop (i + 1) else Some text.[i] in
  loop start

let pattern_binder_tokens_from_text_slice text start stop =
  let stop = min stop (String.length text) in
  let rec take_ident j = if j < stop && is_ident_char text.[j] then take_ident (j + 1) else j in
  let annotation_skip_next_depth depth = function Some skip_depth when depth < skip_depth -> None | skip -> skip in
  let alias_next_depth depth = function
    | Some alias_depth when depth < alias_depth -> None
    | alias_next -> alias_next
  in
  let rec loop i depth skip alias_next acc =
    let skip = annotation_skip_next_depth depth skip in
    let alias_next = alias_next_depth depth alias_next in
    if i >= stop then List.rev acc
    else (
      match text.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1) skip alias_next acc
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1)) skip alias_next acc
      | ',' ->
          let skip = match skip with Some skip_depth when depth <= skip_depth -> None | _ -> skip in
          let alias_next =
            match alias_next with Some alias_depth when depth <= alias_depth -> None | _ -> alias_next
          in
          loop (i + 1) depth skip alias_next acc
      | ':' when i + 1 < stop && text.[i + 1] = ':' -> loop (i + 2) depth skip alias_next acc
      | ':' -> loop (i + 1) depth (Some depth) None acc
      | c when is_ident_char c ->
          let j = take_ident (i + 1) in
          let token = String.sub text i (j - i) in
          let next_char = next_nonspace_char_text text j stop in
          let starts_type_or_constructor =
            match next_char with Some ('(' | '{') -> true | Some '[' -> not (is_pattern_binder token) | _ -> false
          in
          let starts_field_label = match next_char with Some '=' -> true | _ -> false in
          let is_pending_alias =
            match alias_next with Some alias_depth when alias_depth = depth -> true | _ -> false
          in
          let acc =
            if
              Option.is_none skip
              && ((not is_pending_alias) || is_pattern_binder token)
              && is_pattern_binder token && (not starts_type_or_constructor) && not starts_field_label
            then (token, i, j) :: acc
            else acc
          in
          let skip, alias_next =
            if token = "as" then if as_can_introduce_alias text i skip then (None, Some depth) else (Some depth, None)
            else if is_pending_alias then (
              let skip = if starts_type_or_constructor || not (is_pattern_binder token) then Some depth else skip in
              (skip, None)
            )
            else (skip, alias_next)
          in
          loop j depth skip alias_next acc
      | _ -> loop (i + 1) depth skip alias_next acc
    )
  in
  loop start 0 None None []

let local_let_binding_tokens_from_line line =
  match read_token line 0 with
  | Some (("let" | "var"), _, binder_keyword_stop) ->
      let pattern_start =
        match read_token line binder_keyword_stop with
        | Some ("mut", _, mut_stop) -> mut_stop
        | _ -> binder_keyword_stop
      in
      pattern_binder_tokens_from_slice line pattern_start (local_let_pattern_end line pattern_start)
  | _ -> []

let line_indent line =
  let rec loop i = if i < String.length line && is_space line.[i] then loop (i + 1) else i in
  loop 0

let top_level_match_arm_arrow_index line =
  let len = String.length line in
  let rec loop i depth =
    if i + 1 >= len then None
    else (
      match line.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1)
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1))
      | '=' when depth = 0 && line.[i + 1] = '>' -> Some i
      | _ -> loop (i + 1) depth
    )
  in
  loop 0 0

let match_arm_arrows line =
  let len = String.length line in
  let rec loop i depth acc =
    if i + 1 >= len then List.rev acc
    else (
      match line.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1) acc
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1)) acc
      | '=' when line.[i + 1] = '>' -> loop (i + 2) depth ((i, depth) :: acc)
      | _ -> loop (i + 1) depth acc
    )
  in
  loop 0 0 []

let previous_match_arm_pattern_start line arrow arrow_depth =
  let rec skip_space i = if i < arrow && is_space line.[i] then skip_space (i + 1) else i in
  let rec loop i depth start =
    if i >= arrow then skip_space start
    else (
      match line.[i] with
      | '(' | '[' -> loop (i + 1) (depth + 1) start
      | ')' | ']' -> loop (i + 1) (max 0 (depth - 1)) start
      | '{' ->
          let next_depth = depth + 1 in
          let start = if next_depth = arrow_depth then i + 1 else start in
          loop (i + 1) next_depth start
      | '}' -> loop (i + 1) (max 0 (depth - 1)) start
      | ',' when depth = arrow_depth -> loop (i + 1) depth (i + 1)
      | _ -> loop (i + 1) depth start
    )
  in
  loop 0 0 (line_indent line)

let next_match_arm_end line arrow arrow_depth =
  let len = String.length line in
  let rec loop i depth =
    if i >= len then len
    else (
      match line.[i] with
      | ',' when depth = arrow_depth -> i
      | '}' when depth = arrow_depth -> i
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1)
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1))
      | _ -> loop (i + 1) depth
    )
  in
  loop (arrow + 2) arrow_depth

let match_arm_guard_start line start stop =
  let rec loop i depth =
    if i >= stop then None
    else (
      match line.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1)
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1))
      | c when depth = 0 && is_ident_char c ->
          let rec take_ident j = if j < stop && is_ident_char line.[j] then take_ident (j + 1) else j in
          let j = take_ident (i + 1) in
          if String.sub line i (j - i) = "if" then Some i else loop j depth
      | _ -> loop (i + 1) depth
    )
  in
  loop start 0

let match_arm_pattern_start line start stop =
  match read_token line start with
  | Some (("forwards" | "backwards"), _, token_stop) when token_stop <= stop -> token_stop
  | _ -> start

let match_arm_pattern_start_offset text start stop =
  match read_token_from_text text start stop with
  | Some (("forwards" | "backwards"), _, token_stop) when token_stop <= stop -> token_stop
  | _ -> start

let match_arm_binding_tokens_for_arrow line arrow arrow_depth =
  let start =
    previous_match_arm_pattern_start line arrow arrow_depth |> fun start -> match_arm_pattern_start line start arrow
  in
  let stop = match match_arm_guard_start line start arrow with Some guard -> guard | None -> arrow in
  pattern_binder_tokens_from_slice line start stop

let match_arm_binding_tokens_all_from_line line =
  match_arm_arrows line
  |> List.concat_map (fun (arrow, arrow_depth) -> match_arm_binding_tokens_for_arrow line arrow arrow_depth)

let match_arm_binding_tokens_from_line line =
  match top_level_match_arm_arrow_index line with
  | None -> None
  | Some arrow ->
      let indent = line_indent line in
      let start = match_arm_pattern_start line indent arrow in
      let stop = match match_arm_guard_start line start arrow with Some guard -> guard | None -> arrow in
      Some (pattern_binder_tokens_from_slice line start stop)

let match_arm_binding_tokens_for_position line character =
  let cursor = min character (String.length line) in
  let active_binding_groups =
    match_arm_arrows line
    |> List.filter_map (fun (arrow, arrow_depth) ->
        let raw_start = previous_match_arm_pattern_start line arrow arrow_depth in
        let start = match_arm_pattern_start line raw_start arrow in
        let arm_end = next_match_arm_end line arrow arrow_depth in
        let bindings = match_arm_binding_tokens_for_arrow line arrow arrow_depth in
        let stop = match match_arm_guard_start line start arrow with Some guard -> guard | None -> arrow in
        if (stop < arrow && cursor >= stop && cursor <= arrow) || (cursor >= arrow + 2 && cursor <= arm_end) then
          Some bindings
        else None
    )
  in
  match active_binding_groups with [] -> None | groups -> Some (List.concat groups)

type match_arm_binding_token = {
  match_arm_binding_name : string;
  match_arm_binding_start : int;
  match_arm_binding_stop : int;
  match_arm_active_start : int;
  match_arm_active_stop : int;
}

let delimiter_depths text =
  let len = String.length text in
  let depths = Array.make (len + 1) 0 in
  let rec loop i depth =
    depths.(i) <- depth;
    if i < len then (
      let next_depth =
        match text.[i] with '(' | '[' | '{' -> depth + 1 | ')' | ']' | '}' -> max 0 (depth - 1) | _ -> depth
      in
      loop (i + 1) next_depth
    )
  in
  loop 0 0;
  depths

let text_match_arm_arrows text depths =
  let len = String.length text in
  let rec loop i acc =
    if i + 1 >= len then List.rev acc
    else if text.[i] = '=' && text.[i + 1] = '>' then loop (i + 2) ((i, depths.(i)) :: acc)
    else loop (i + 1) acc
  in
  loop 0 []

let previous_match_arm_pattern_start_offset text depths arrow arrow_depth =
  let rec skip_space i = if i < arrow && is_space text.[i] then skip_space (i + 1) else i in
  let rec loop i =
    if i < 0 then skip_space 0
    else (
      match text.[i] with
      | ',' when depths.(i) = arrow_depth -> skip_space (i + 1)
      | '{' when depths.(i + 1) = arrow_depth -> skip_space (i + 1)
      | _ -> loop (i - 1)
    )
  in
  loop (arrow - 1)

let next_match_arm_end_offset text depths arrow arrow_depth =
  let len = String.length text in
  let rec loop i =
    if i >= len then len
    else (
      match text.[i] with
      | ',' when depths.(i) = arrow_depth -> i
      | '}' when depths.(i) = arrow_depth -> i
      | _ -> loop (i + 1)
    )
  in
  loop (arrow + 2)

let match_arm_guard_start_offset text depths start stop arrow_depth =
  let stop = min stop (String.length text) in
  let rec loop i =
    if i >= stop then None
    else (
      match text.[i] with
      | c when depths.(i) = arrow_depth && is_ident_char c ->
          let rec take_ident j = if j < stop && is_ident_char text.[j] then take_ident (j + 1) else j in
          let j = take_ident (i + 1) in
          if String.sub text i (j - i) = "if" then Some i else loop j
      | _ -> loop (i + 1)
    )
  in
  loop start

let match_arm_binding_tokens_from_text text =
  let depths = delimiter_depths text in
  text_match_arm_arrows text depths
  |> List.concat_map (fun (arrow, arrow_depth) ->
      let raw_start = previous_match_arm_pattern_start_offset text depths arrow arrow_depth in
      let pattern_start = match_arm_pattern_start_offset text raw_start arrow in
      let active_stop = next_match_arm_end_offset text depths arrow arrow_depth in
      let pattern_stop =
        match match_arm_guard_start_offset text depths pattern_start arrow arrow_depth with
        | Some guard -> guard
        | None -> arrow
      in
      let active_start = if pattern_stop < arrow then pattern_stop else arrow + 2 in
      pattern_binder_tokens_from_text_slice text pattern_start pattern_stop
      |> List.map (fun (name, start, stop) ->
          {
            match_arm_binding_name = name;
            match_arm_binding_start = start;
            match_arm_binding_stop = stop;
            match_arm_active_start = active_start;
            match_arm_active_stop = active_stop;
          }
      )
  )

let match_arm_binding_tokens_in_scope text position =
  let cursor = offset_of_position text position in
  match_arm_binding_tokens_from_text text
  |> List.filter (fun binding -> binding.match_arm_active_start <= cursor && cursor <= binding.match_arm_active_stop)
  |> List.map (fun binding ->
      let start_pos = position_of_offset text binding.match_arm_binding_start in
      let end_pos = position_of_offset text binding.match_arm_binding_stop in
      (binding.match_arm_binding_name, start_pos.line, start_pos.character, end_pos.character)
  )

type mapping_binding_token = {
  mapping_binding_name : string;
  mapping_binding_start : int;
  mapping_binding_stop : int;
  mapping_active_start : int;
  mapping_active_stop : int;
}

let line_start_offset text offset =
  let rec loop i = if i <= 0 then 0 else if text.[i - 1] = '\n' then i else loop (i - 1) in
  loop (min offset (String.length text))

let line_first_nonspace_offset text line_start =
  let len = String.length text in
  let rec loop i =
    if i >= len || text.[i] = '\n' then None
    else if text.[i] = ' ' || text.[i] = '\t' || text.[i] = '\r' then loop (i + 1)
    else Some i
  in
  loop line_start

let previous_top_level_equals text depths offset =
  let rec loop i = if i < 0 then None else if text.[i] = '=' && depths.(i) = 0 then Some i else loop (i - 1) in
  loop (offset - 1)

let mapping_clause_prefix_before_equals text equals =
  let start = line_start_offset text equals in
  let prefix = String.sub text start (equals - start) in
  match tokens_from prefix 0 |> token_texts with "mapping" :: "clause" :: _ -> true | _ -> false

let has_top_level_declaration_between text equals arrow =
  let rec loop i =
    if i >= arrow then false
    else if text.[i] = '\n' then (
      let line_start = i + 1 in
      match line_first_nonspace_offset text line_start with
      | Some first when first = line_start && not (text_starts_with_keyword text first "when") -> true
      | _ -> loop line_start
    )
    else loop (i + 1)
  in
  loop (equals + 1)

let mapping_arrow_is_clause text depths arrow arrow_depth =
  arrow_depth > 0
  ||
  match previous_top_level_equals text depths arrow with
  | Some equals ->
      mapping_clause_prefix_before_equals text equals && not (has_top_level_declaration_between text equals arrow)
  | None -> false

let text_mapping_arrows text depths =
  let len = String.length text in
  let rec loop i acc =
    if i + 2 >= len then List.rev acc
    else if text.[i] = '<' && text.[i + 1] = '-' && text.[i + 2] = '>' then (
      let arrow_depth = depths.(i) in
      let acc = if mapping_arrow_is_clause text depths i arrow_depth then (i, arrow_depth) :: acc else acc in
      loop (i + 3) acc
    )
    else loop (i + 1) acc
  in
  loop 0 []

let previous_mapping_pattern_start_offset text depths arrow arrow_depth =
  let rec skip_space i = if i < arrow && is_space text.[i] then skip_space (i + 1) else i in
  let rec loop i =
    if i < 0 then skip_space 0
    else (
      match text.[i] with
      | ',' when depths.(i) = arrow_depth -> skip_space (i + 1)
      | ';' when depths.(i) = arrow_depth -> skip_space (i + 1)
      | '=' when depths.(i) = arrow_depth -> skip_space (i + 1)
      | '{' when depths.(i + 1) = arrow_depth -> skip_space (i + 1)
      | _ -> loop (i - 1)
    )
  in
  loop (arrow - 1)

let mapping_clause_line_continues text newline =
  let line_start = newline + 1 in
  match line_first_nonspace_offset text line_start with
  | None -> false
  | Some first when first > line_start -> true
  | Some first -> text_starts_with_keyword text first "when"

let next_mapping_clause_end_offset text depths arrow arrow_depth =
  let len = String.length text in
  let rec loop i =
    if i >= len then len
    else (
      match text.[i] with
      | ',' when depths.(i) = arrow_depth -> i
      | ';' when depths.(i) = arrow_depth -> i
      | '}' when depths.(i) = arrow_depth -> i
      | '\n' when arrow_depth = 0 && not (mapping_clause_line_continues text i) -> i
      | _ -> loop (i + 1)
    )
  in
  loop (arrow + 3)

let mapping_binding_tokens_from_text text =
  let depths = delimiter_depths text in
  text_mapping_arrows text depths
  |> List.concat_map (fun (arrow, arrow_depth) ->
      let raw_start = previous_mapping_pattern_start_offset text depths arrow arrow_depth in
      let pattern_start = match_arm_pattern_start_offset text raw_start arrow in
      let active_stop = next_mapping_clause_end_offset text depths arrow arrow_depth in
      let pattern_stop =
        match match_arm_guard_start_offset text depths pattern_start arrow arrow_depth with
        | Some guard -> guard
        | None -> arrow
      in
      let active_start = if pattern_stop < arrow then pattern_stop else arrow + 3 in
      pattern_binder_tokens_from_text_slice text pattern_start pattern_stop
      |> List.map (fun (name, start, stop) ->
          {
            mapping_binding_name = name;
            mapping_binding_start = start;
            mapping_binding_stop = stop;
            mapping_active_start = active_start;
            mapping_active_stop = active_stop;
          }
      )
  )

let mapping_binding_tokens_in_scope text position =
  let cursor = offset_of_position text position in
  mapping_binding_tokens_from_text text
  |> List.filter (fun binding -> binding.mapping_active_start <= cursor && cursor <= binding.mapping_active_stop)
  |> List.map (fun binding ->
      let start_pos = position_of_offset text binding.mapping_binding_start in
      let end_pos = position_of_offset text binding.mapping_binding_stop in
      (binding.mapping_binding_name, start_pos.line, start_pos.character, end_pos.character)
  )

type loop_binding_token = {
  loop_binding_name : string;
  loop_binding_start : int;
  loop_binding_stop : int;
  loop_active_start : int;
  loop_active_stop : int;
}

let next_nonspace_offset text start stop =
  let stop = min stop (String.length text) in
  let rec loop i = if i >= stop then None else if is_space text.[i] then loop (i + 1) else Some i in
  loop start

let find_matching_delimiter text open_index open_ch close_ch =
  let len = String.length text in
  if open_index < 0 || open_index >= len || text.[open_index] <> open_ch then None
  else (
    let rec loop i depth =
      if i >= len then None
      else (
        match text.[i] with
        | c when c = open_ch -> loop (i + 1) (depth + 1)
        | c when c = close_ch -> if depth = 1 then Some i else loop (i + 1) (max 0 (depth - 1))
        | _ -> loop (i + 1) depth
      )
    in
    loop open_index 0
  )

let find_top_level_keyword_offset text depths start stop keyword depth =
  let stop = min stop (String.length text) in
  let rec loop i =
    if i >= stop then None
    else if depths.(i) = depth && text_starts_with_keyword text i keyword then Some i
    else loop (i + 1)
  in
  loop start

let find_statement_end_offset text depths start =
  let len = String.length text in
  let depth = depths.(min start len) in
  let rec loop i = if i >= len then len else if text.[i] = ';' && depths.(i) = depth then i else loop (i + 1) in
  loop start

let foreach_loop_body_range text close_paren =
  let len = String.length text in
  let depths = delimiter_depths text in
  match next_nonspace_offset text (close_paren + 1) len with
  | Some body_start when text.[body_start] = '{' ->
      Option.map (fun body_stop -> (body_start + 1, body_stop)) (find_matching_delimiter text body_start '{' '}')
  | Some body_start -> Some (body_start, find_statement_end_offset text depths body_start)
  | None -> None

let foreach_loop_bindings_from_text text =
  let len = String.length text in
  let depths = delimiter_depths text in
  let rec loop i acc =
    if i >= len then List.rev acc
    else if text_starts_with_keyword text i "foreach" then (
      let acc =
        match next_nonspace_offset text (i + String.length "foreach") len with
        | Some open_paren when text.[open_paren] = '(' -> (
            match find_matching_delimiter text open_paren '(' ')' with
            | Some close_paren -> (
                match foreach_loop_body_range text close_paren with
                | Some (active_start, active_stop) ->
                    let header_depth = depths.(min (open_paren + 1) len) in
                    let pattern_stop =
                      find_top_level_keyword_offset text depths (open_paren + 1) close_paren "from" header_depth
                      |> Option.value ~default:close_paren
                    in
                    pattern_binder_tokens_from_text_slice text (open_paren + 1) pattern_stop
                    |> List.fold_left
                         (fun acc (name, start, stop) ->
                           {
                             loop_binding_name = name;
                             loop_binding_start = start;
                             loop_binding_stop = stop;
                             loop_active_start = active_start;
                             loop_active_stop = active_stop;
                           }
                           :: acc
                         )
                         acc
                | None -> acc
              )
            | None -> acc
          )
        | _ -> acc
      in
      loop (i + String.length "foreach") acc
    )
    else loop (i + 1) acc
  in
  loop 0 []

let loop_binding_tokens_in_scope text position =
  let cursor = offset_of_position text position in
  foreach_loop_bindings_from_text text
  |> List.filter (fun binding -> binding.loop_active_start <= cursor && cursor <= binding.loop_active_stop)
  |> List.map (fun binding ->
      let start_pos = position_of_offset text binding.loop_binding_start in
      let end_pos = position_of_offset text binding.loop_binding_stop in
      (binding.loop_binding_name, start_pos.line, start_pos.character, end_pos.character)
  )

let split_top_level_by is_separator s =
  let len = String.length s in
  let rec add_piece start stop acc =
    let piece = String.sub s start (stop - start) |> String.trim in
    if piece = "" then acc else piece :: acc
  in
  let rec loop i depth start acc =
    if i >= len then List.rev (add_piece start len acc)
    else (
      match s.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1) start acc
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1)) start acc
      | c when depth = 0 && is_separator c -> loop (i + 1) depth (i + 1) (add_piece start i acc)
      | _ -> loop (i + 1) depth start acc
    )
  in
  loop 0 0 0 []

let split_top_level_commas = split_top_level_by (fun c -> c = ',')

let split_decl_items = split_top_level_by (fun c -> c = ',' || c = '|')

let split_top_level_comma_ranges line start stop =
  let stop = min stop (String.length line) in
  let rec trim_start i = if i >= stop || not (is_space line.[i]) then i else trim_start (i + 1) in
  let rec trim_stop i = if i <= start || not (is_space line.[i - 1]) then i else trim_stop (i - 1) in
  let add_range start stop acc =
    let start = trim_start start in
    let stop = trim_stop stop in
    if start >= stop then acc else (start, stop) :: acc
  in
  let rec loop i depth start acc =
    if i >= stop then List.rev (add_range start stop acc)
    else (
      match line.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1) start acc
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1)) start acc
      | ',' when depth = 0 -> loop (i + 1) depth (i + 1) (add_range start i acc)
      | _ -> loop (i + 1) depth start acc
    )
  in
  loop start 0 start []

let strip_line_comment s =
  let len = String.length s in
  let rec loop i =
    if i + 1 >= len then s else if s.[i] = '/' && s.[i + 1] = '/' then String.sub s 0 i else loop (i + 1)
  in
  loop 0

let strip_block_comments s =
  let len = String.length s in
  let buffer = Buffer.create len in
  let rec copy i =
    if i >= len then ()
    else if i + 1 < len && s.[i] = '/' && s.[i + 1] = '*' then skip (i + 2)
    else (
      Buffer.add_char buffer s.[i];
      copy (i + 1)
    )
  and skip i =
    if i >= len then () else if i + 1 < len && s.[i] = '*' && s.[i + 1] = '/' then copy (i + 2) else skip (i + 1)
  in
  copy 0;
  Buffer.contents buffer

let clean_completion_decl_piece s =
  strip_line_comment s |> strip_block_comments |> String.map (function '{' | '}' -> ' ' | c -> c) |> String.trim

let source_name_from_decl_piece piece =
  let piece = clean_completion_decl_piece piece in
  let lhs = match split_once_char ':' piece with Some (lhs, _) -> lhs | None -> piece in
  let lhs = match split_once_char '=' lhs with Some (lhs, _) -> lhs | None -> lhs in
  tokens_from lhs 0 |> token_texts |> List.find_opt is_completion_binder

let source_type_from_decl_piece piece =
  match split_once_char ':' piece with
  | Some (_, rhs) ->
      let rhs = clean_completion_decl_piece rhs in
      if rhs = "" then None else Some rhs
  | None -> None

let assignment_index_before_cursor line cursor =
  let stop = min cursor (String.length line) in
  let rec loop i depth last =
    if i >= stop then last
    else (
      match line.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1) last
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1)) last
      | '='
        when depth = 0
             && (i = 0 || not (List.mem line.[i - 1] ['<'; '>'; '!'; '=']))
             && (i + 1 >= String.length line || line.[i + 1] <> '>') ->
          loop (i + 1) depth (Some i)
      | _ -> loop (i + 1) depth last
    )
  in
  loop 0 0 None

let clean_expected_type_name s =
  clean_completion_decl_piece s |> String.map (function ';' -> ' ' | c -> c) |> String.trim

let clean_type_name_for_match s =
  clean_expected_type_name s |> String.map (function ',' | ';' -> ' ' | c -> c) |> String.trim

let expected_type_from_lhs lhs =
  let tokens = tokens_from lhs 0 |> drop_leading_decl_modifiers |> token_texts in
  match last_substring_index ~needle:"->" lhs with
  | Some arrow when List.mem "function" tokens || List.mem "clause" tokens ->
      let ty = String.sub lhs (arrow + 2) (String.length lhs - arrow - 2) |> clean_expected_type_name in
      if ty = "" then None else Some ty
  | _ when List.mem "let" tokens || List.mem "var" tokens -> (
      match last_index_of_char ':' lhs with
      | Some colon ->
          let ty = String.sub lhs (colon + 1) (String.length lhs - colon - 1) |> clean_expected_type_name in
          if ty = "" then None else Some ty
      | None -> None
    )
  | _ -> None

let completion_expected_type text position =
  match line_at text position.line with
  | None -> None
  | Some line -> (
      let cursor = min position.character (String.length line) in
      match assignment_index_before_cursor line cursor with
      | None -> None
      | Some equals ->
          let lhs = String.sub line 0 equals in
          expected_type_from_lhs lhs
    )

let completion_type_short_name ty =
  let ty = clean_type_name_for_match ty in
  match last_index_of_char '.' ty with
  | Some dot when dot + 1 < String.length ty -> String.sub ty (dot + 1) (String.length ty - dot - 1)
  | _ -> ty

let completion_type_matches_owner expected owner =
  String.equal (completion_type_short_name expected) (completion_type_short_name owner)

let completion_decl_sort_group ?expected_type owner default_group =
  match expected_type with Some expected when completion_type_matches_owner expected owner -> 0 | _ -> default_group

let find_matching_paren s open_index =
  let len = String.length s in
  let rec loop i depth =
    if i >= len then None
    else (
      match s.[i] with
      | '(' -> loop (i + 1) (depth + 1)
      | ')' when depth = 1 -> Some i
      | ')' -> loop (i + 1) (max 0 (depth - 1))
      | _ -> loop (i + 1) depth
    )
  in
  loop open_index 0

type function_header_binding_kind = Parameter_binding | Function_pattern_binding

type function_header_binding_token = {
  function_header_binding_name : string;
  function_header_binding_start : int;
  function_header_binding_stop : int;
  function_header_binding_kind : function_header_binding_kind;
}

let top_level_function_header_stop line start =
  let len = String.length line in
  let rec loop i depth =
    if i >= len then len
    else (
      match line.[i] with
      | '(' | '[' | '{' -> loop (i + 1) (depth + 1)
      | ')' | ']' | '}' -> loop (i + 1) (max 0 (depth - 1))
      | '=' when depth = 0 -> i
      | '-' when depth = 0 && i + 1 < len && line.[i + 1] = '>' -> i
      | _ -> loop (i + 1) depth
    )
  in
  loop start 0

let function_header_name_stop line =
  let tokens = tokens_from line 0 |> drop_leading_decl_modifiers in
  match tokens with
  | ("function", _, _) :: ("clause", _, _) :: (_, _, stop) :: _
  | ("function", _, _) :: (_, _, stop) :: _
  | ("scattered", _, _) :: ("function", _, _) :: (_, _, stop) :: _ ->
      Some stop
  | _ -> None

let function_header_binding_regions line =
  match function_header_name_stop line with
  | None -> []
  | Some start ->
      let header_stop = top_level_function_header_stop line start in
      let rec paren_regions i acc =
        if i >= header_stop then List.rev acc
        else if line.[i] = '(' then (
          match find_matching_paren line i with
          | Some close_index when close_index <= header_stop ->
              let bindings = pattern_binder_tokens_from_slice line (i + 1) close_index in
              let acc = if bindings = [] then acc else (i + 1, close_index) :: acc in
              paren_regions (close_index + 1) acc
          | _ -> paren_regions (i + 1) acc
        )
        else paren_regions (i + 1) acc
      in
      let regions = paren_regions start [] in
      if regions <> [] then regions else if start < header_stop then [(start, header_stop)] else []

let function_header_segment_is_simple_parameter line start stop bindings =
  match bindings with
  | [(_, binding_start, binding_stop)] ->
      let first_token =
        match tokens_from (String.sub line start (stop - start)) 0 with
        | (token, token_start, token_stop) :: _ -> Some (token, start + token_start, start + token_stop)
        | [] -> None
      in
      first_token = Some (String.sub line binding_start (binding_stop - binding_start), binding_start, binding_stop)
  | _ -> false

let function_header_binding_tokens_from_line line =
  function_header_binding_regions line
  |> List.concat_map (fun (start, stop) ->
      split_top_level_comma_ranges line start stop
      |> List.concat_map (fun (segment_start, segment_stop) ->
          let bindings = pattern_binder_tokens_from_slice line segment_start segment_stop in
          let kind =
            if function_header_segment_is_simple_parameter line segment_start segment_stop bindings then
              Parameter_binding
            else Function_pattern_binding
          in
          bindings
          |> List.map (fun (name, binding_start, binding_stop) ->
              {
                function_header_binding_name = name;
                function_header_binding_start = binding_start;
                function_header_binding_stop = binding_stop;
                function_header_binding_kind = kind;
              }
          )
      )
  )

let function_header_parameter_names line =
  function_header_binding_tokens_from_line line
  |> List.filter_map (fun binding ->
      match binding.function_header_binding_kind with
      | Parameter_binding -> Some binding.function_header_binding_name
      | Function_pattern_binding -> None
  )
  |> unique_strings

let function_header_parameter_types line =
  function_header_binding_regions line
  |> List.concat_map (fun (start, stop) ->
      split_top_level_comma_ranges line start stop
      |> List.filter_map (fun (segment_start, segment_stop) ->
          let bindings = pattern_binder_tokens_from_slice line segment_start segment_stop in
          if function_header_segment_is_simple_parameter line segment_start segment_stop bindings then (
            let piece = String.sub line segment_start (segment_stop - segment_start) in
            match (source_name_from_decl_piece piece, source_type_from_decl_piece piece) with
            | Some name, Some ty -> Some (name, clean_expected_type_name ty)
            | _ -> None
          )
          else None
      )
  )

let function_header_pattern_names line =
  function_header_binding_tokens_from_line line
  |> List.filter_map (fun binding ->
      match binding.function_header_binding_kind with
      | Parameter_binding -> None
      | Function_pattern_binding -> Some binding.function_header_binding_name
  )
  |> unique_strings

let local_typed_binding_from_line line =
  match read_token line 0 with
  | Some (("let" | "var"), _, keyword_stop) -> (
      let pattern_start =
        match read_token line keyword_stop with Some ("mut", _, mut_stop) -> mut_stop | _ -> keyword_stop
      in
      let cursor = String.length line in
      match assignment_index_before_cursor line cursor with
      | Some equals when equals > pattern_start -> (
          let piece = String.sub line pattern_start (equals - pattern_start) in
          match (source_name_from_decl_piece piece, source_type_from_decl_piece piece) with
          | Some name, Some ty -> Some (name, clean_expected_type_name ty)
          | _ -> None
        )
      | _ -> None
    )
  | _ -> None

let completion_local_typed_bindings text position =
  let lines = lines_of_text text in
  let start_line = completion_scope_start_line text position in
  let line_prefix line_no line =
    if line_no = position.line then String.sub line 0 (min position.character (String.length line)) else line
  in
  let rec loop line_no acc =
    if line_no > position.line then List.rev acc
    else (
      let acc =
        match List.nth_opt lines line_no with
        | Some line when line_no > start_line && line <> "" && is_space line.[0] -> (
            match local_typed_binding_from_line (line_prefix line_no line) with
            | Some binding -> binding :: acc
            | None -> acc
          )
        | _ -> acc
      in
      loop (line_no + 1) acc
    )
  in
  loop start_line []

let completion_name_type_in_scope text position name =
  match
    List.find_opt (fun (candidate, _) -> candidate = name) (List.rev (completion_local_typed_bindings text position))
  with
  | Some (_, ty) -> Some ty
  | None -> (
      match line_at text (completion_scope_start_line text position) with
      | Some line ->
          Option.map snd (List.find_opt (fun (candidate, _) -> candidate = name) (function_header_parameter_types line))
      | None -> None
    )

let completion_parameter_names text position prefix =
  match line_at text (completion_scope_start_line text position) with
  | None -> []
  | Some line -> function_header_parameter_names line |> List.filter (fun name -> lowercase_starts_with name prefix)

let completion_function_pattern_names text position prefix =
  match line_at text (completion_scope_start_line text position) with
  | None -> []
  | Some line -> function_header_pattern_names line |> List.filter (fun name -> lowercase_starts_with name prefix)

let completion_local_let_names text position prefix =
  let lines = lines_of_text text in
  let start_line = completion_scope_start_line text position in
  let line_prefix line_no line =
    if line_no = position.line then String.sub line 0 (min position.character (String.length line)) else line
  in
  let rec loop line_no acc =
    if line_no > position.line then List.rev acc
    else (
      let acc =
        match List.nth_opt lines line_no with
        | Some line when line_no > start_line && line <> "" && is_space line.[0] ->
            local_let_binding_tokens_from_line (line_prefix line_no line)
            |> List.fold_left
                 (fun acc (name, _, _) -> if lowercase_starts_with name prefix then name :: acc else acc)
                 acc
        | _ -> acc
      in
      loop (line_no + 1) acc
    )
  in
  unique_strings (loop start_line [])

let completion_match_arm_names text position prefix =
  match_arm_binding_tokens_in_scope text position
  |> List.filter_map (fun (name, _, _, _) -> if lowercase_starts_with name prefix then Some name else None)
  |> unique_strings

let completion_mapping_names text position prefix =
  mapping_binding_tokens_in_scope text position
  |> List.filter_map (fun (name, _, _, _) -> if lowercase_starts_with name prefix then Some name else None)
  |> unique_strings

let completion_loop_names text position prefix =
  loop_binding_tokens_in_scope text position
  |> List.filter_map (fun (name, _, _, _) -> if lowercase_starts_with name prefix then Some name else None)
  |> unique_strings

let body_after_equals lines line_no line =
  match String.index_opt line '=' with
  | None -> []
  | Some equals ->
      let first = String.sub line (equals + 1) (String.length line - equals - 1) in
      if String.contains first '{' && not (String.contains first '}') then (
        let rec collect current acc =
          match List.nth_opt lines current with
          | None -> List.rev acc
          | Some body_line ->
              let acc = body_line :: acc in
              if String.contains body_line '}' then List.rev acc else collect (current + 1) acc
        in
        first :: collect (line_no + 1) []
      )
      else [first]

let strip_outer_brace_block s =
  let len = String.length s in
  let rec first_non_space i = if i >= len then None else if is_space s.[i] then first_non_space (i + 1) else Some i in
  let rec last_non_space i = if i < 0 then None else if is_space s.[i] then last_non_space (i - 1) else Some i in
  match (first_non_space 0, last_non_space (len - 1)) with
  | Some first, Some last when first < last && s.[first] = '{' && s.[last] = '}' ->
      String.sub s (first + 1) (last - first - 1)
  | _ -> s

let completion_body_text lines line_no line =
  body_after_equals lines line_no line |> String.concat "\n" |> strip_outer_brace_block

let enum_name_from_tokens = function
  | "enum" :: "clause" :: enum_name :: _ -> Some enum_name
  | "enum" :: enum_name :: _ when enum_name <> "with" -> Some enum_name
  | _ -> None

let union_name_from_tokens = function
  | "union" :: "clause" :: union_name :: _ -> Some union_name
  | "union" :: union_name :: _ when union_name <> "with" -> Some union_name
  | "newtype" :: newtype_name :: _ -> Some newtype_name
  | _ -> None

let struct_name_from_tokens = function "struct" :: struct_name :: _ -> Some struct_name | _ -> None

let enum_completion_items_from_doc ?expected_type doc prefix =
  let lines = lines_of_text doc.doc_text in
  lines
  |> List.mapi (fun line_no line ->
      let tokens = tokens_from line 0 |> drop_leading_decl_modifiers |> token_texts in
      match enum_name_from_tokens tokens with
      | None -> []
      | Some enum_name ->
          completion_body_text lines line_no line |> split_decl_items
          |> List.filter_map (fun piece ->
              Option.bind (source_name_from_decl_piece piece) (fun member ->
                  if lowercase_starts_with member prefix then (
                    let sort_group = completion_decl_sort_group ?expected_type enum_name 1 in
                    Some
                      (completion_source_item_json ~label:member ~kind:20 ~detail:("enum member of " ^ enum_name)
                         ~sort_group
                      )
                  )
                  else None
              )
          )
  )
  |> List.concat

let union_completion_items_from_doc ?expected_type doc prefix =
  let lines = lines_of_text doc.doc_text in
  lines
  |> List.mapi (fun line_no line ->
      let tokens = tokens_from line 0 |> drop_leading_decl_modifiers |> token_texts in
      match union_name_from_tokens tokens with
      | None -> []
      | Some union_name ->
          completion_body_text lines line_no line |> split_decl_items
          |> List.filter_map (fun piece ->
              Option.bind (source_name_from_decl_piece piece) (fun constructor ->
                  if lowercase_starts_with constructor prefix then (
                    let sort_group = completion_decl_sort_group ?expected_type union_name 1 in
                    Some
                      (completion_source_item_json ~label:constructor ~kind:4
                         ~detail:("union constructor of " ^ union_name) ~sort_group
                      )
                  )
                  else None
              )
          )
  )
  |> List.concat

let field_completion_items_from_doc ?receiver_type doc prefix =
  let lines = lines_of_text doc.doc_text in
  lines
  |> List.mapi (fun line_no line ->
      let tokens = tokens_from line 0 |> drop_leading_decl_modifiers |> token_texts in
      match struct_name_from_tokens tokens with
      | None -> []
      | Some struct_name ->
          completion_body_text lines line_no line |> split_top_level_commas
          |> List.filter_map (fun piece ->
              Option.bind (source_name_from_decl_piece piece) (fun field ->
                  if lowercase_starts_with field prefix then (
                    let detail =
                      match source_type_from_decl_piece piece with
                      | Some ty -> Printf.sprintf "field of %s : %s" struct_name ty
                      | None -> "field of " ^ struct_name
                    in
                    let sort_group =
                      match receiver_type with
                      | Some ty -> completion_decl_sort_group ~expected_type:ty struct_name 1
                      | None -> 1
                    in
                    Some (completion_source_item_json ~label:field ~kind:5 ~detail ~sort_group)
                  )
                  else None
              )
          )
  )
  |> List.concat

let struct_field_type_from_doc doc owner_type field_name =
  let lines = lines_of_text doc.doc_text in
  let rec loop line_no =
    match List.nth_opt lines line_no with
    | None -> None
    | Some line -> (
        let tokens = tokens_from line 0 |> drop_leading_decl_modifiers |> token_texts in
        match struct_name_from_tokens tokens with
        | Some struct_name when completion_type_matches_owner owner_type struct_name -> (
            match
              completion_body_text lines line_no line |> split_top_level_commas
              |> List.find_map (fun piece ->
                  match (source_name_from_decl_piece piece, source_type_from_decl_piece piece) with
                  | Some field, Some ty when field = field_name -> Some (clean_expected_type_name ty)
                  | _ -> None
              )
            with
            | Some _ as result -> result
            | None -> loop (line_no + 1)
          )
        | _ -> loop (line_no + 1)
      )
  in
  loop 0

let struct_field_type_from_docs docs owner_type field_name =
  List.find_map (fun doc -> struct_field_type_from_doc doc owner_type field_name) docs

let collection_element_type_from_type ty =
  let ty = clean_expected_type_name ty in
  let collection_args type_name =
    let prefix = type_name ^ "(" in
    let prefix_len = String.length prefix in
    if starts_with ~prefix ty && String.length ty > prefix_len && ty.[String.length ty - 1] = ')' then (
      let args = String.sub ty prefix_len (String.length ty - prefix_len - 1) |> split_top_level_commas in
      List.rev args |> List.find_opt (fun arg -> String.trim arg <> "") |> Option.map clean_expected_type_name
    )
    else None
  in
  match collection_args "vector" with Some _ as result -> result | None -> collection_args "list"

let apply_receiver_indexes ty index_count =
  let rec loop ty count =
    if count <= 0 then Some ty
    else Option.bind (collection_element_type_from_type ty) (fun item_ty -> loop item_ty (count - 1))
  in
  loop ty index_count

let completion_return_type_from_type ty =
  match last_substring_index ~needle:"->" ty with
  | Some arrow ->
      let result = String.sub ty (arrow + 2) (String.length ty - arrow - 2) |> clean_expected_type_name in
      if result = "" then None else Some result
  | None -> None

let source_function_return_type_from_line line =
  match last_substring_index ~needle:"->" line with
  | Some arrow ->
      let tail = String.sub line (arrow + 2) (String.length line - arrow - 2) in
      let stop = match String.index_opt tail '=' with Some equals -> equals | None -> String.length tail in
      let result = String.sub tail 0 stop |> clean_expected_type_name in
      if result = "" then None else Some result
  | None -> None

let callable_return_type_from_doc doc name =
  document_symbols doc.doc_uri doc.doc_text
  |> List.find_map (fun symbol ->
      if symbol.name = name then (
        match source_type_for_symbol doc.doc_text symbol with
        | Some ty -> completion_return_type_from_type ty
        | None when symbol.detail = "function" ->
            Option.bind (symbol_source_line doc.doc_text symbol) source_function_return_type_from_line
        | None -> None
      )
      else None
  )

let callable_return_type_from_docs docs name = List.find_map (fun doc -> callable_return_type_from_doc doc name) docs

let previous_non_space_char text offset =
  let rec loop i = if i < 0 then None else if is_space text.[i] then loop (i - 1) else Some text.[i] in
  loop (offset - 1)

let completion_is_struct_literal_context text position prefix =
  match line_at text position.line with
  | None -> false
  | Some line ->
      let stop = max 0 (min (String.length line) (position.character - String.length prefix)) in
      let before = String.sub line 0 stop in
      lowercase_contains before "struct {"

let completion_is_field_context text position prefix =
  let offset = offset_of_position text position - String.length prefix in
  match previous_non_space_char text offset with
  | Some '.' -> true
  | _ -> completion_is_struct_literal_context text position prefix

type completion_receiver_segment =
  | Receiver_name of string * int
  | Receiver_call of string * int
  | Receiver_if of completion_receiver_segment list * completion_receiver_segment list * int

let completion_field_receiver_chain text position prefix =
  let cursor = offset_of_position text position in
  let field_start = max 0 (cursor - String.length prefix) in
  let delimiter_depths_cache = lazy (delimiter_depths text) in
  let rec skip_left i = if i > 0 && is_space text.[i - 1] then skip_left (i - 1) else i in
  let rec skip_right i stop = if i < stop && is_space text.[i] then skip_right (i + 1) stop else i in
  let rec ident_start i = if i > 0 && is_ident_char text.[i - 1] then ident_start (i - 1) else i in
  let rec matching_open_bracket i depth =
    if i < 0 then None
    else (
      match text.[i] with
      | ']' -> matching_open_bracket (i - 1) (depth + 1)
      | '[' when depth = 0 -> Some i
      | '[' -> matching_open_bracket (i - 1) (depth - 1)
      | _ -> matching_open_bracket (i - 1) depth
    )
  in
  let rec matching_open_paren i depth =
    if i < 0 then None
    else (
      match text.[i] with
      | ')' -> matching_open_paren (i - 1) (depth + 1)
      | '(' when depth = 0 -> Some i
      | '(' -> matching_open_paren (i - 1) (depth - 1)
      | _ -> matching_open_paren (i - 1) depth
    )
  in
  let rec strip_index_suffix stop index_count =
    let stop = skip_left stop in
    if stop > 0 && text.[stop - 1] = ']' then (
      match matching_open_bracket (stop - 2) 0 with
      | Some open_bracket -> strip_index_suffix open_bracket (index_count + 1)
      | None -> (stop, index_count)
    )
    else (stop, index_count)
  in
  let add_indexes_to_segment index_count = function
    | Receiver_name (name, existing_count) -> Receiver_name (name, existing_count + index_count)
    | Receiver_call (name, existing_count) -> Receiver_call (name, existing_count + index_count)
    | Receiver_if (then_segments, else_segments, existing_count) ->
        Receiver_if (then_segments, else_segments, existing_count + index_count)
  in
  let add_indexes_to_last_segment index_count segments =
    if index_count <= 0 then segments
    else (
      let rec loop = function
        | [] -> []
        | [segment] -> [add_indexes_to_segment index_count segment]
        | segment :: rest -> segment :: loop rest
      in
      loop segments
    )
  in
  let rec segment_before stop =
    let stop, index_count = strip_index_suffix stop 0 in
    let stop = skip_left stop in
    if stop <= 0 then None
    else if text.[stop - 1] = ')' then (
      match matching_open_paren (stop - 2) 0 with
      | Some open_paren ->
          let name_stop = skip_left open_paren in
          let name_start = ident_start name_stop in
          if name_start < name_stop then
            Some (name_start, [Receiver_call (String.sub text name_start (name_stop - name_start), index_count)])
          else (
            let close_paren = stop - 1 in
            let content_start = skip_right (open_paren + 1) close_paren in
            let content_stop = skip_left close_paren in
            if content_start >= content_stop then None
            else (
              match if_receiver_segments content_start content_stop index_count with
              | Some segments -> Some (open_paren, segments)
              | None -> (
                  match collect_chain close_paren [] with
                  | Some (start, segments) when start = content_start ->
                      Some (open_paren, add_indexes_to_last_segment index_count segments)
                  | _ -> None
                )
            )
          )
      | None -> None
    )
    else (
      let start = ident_start stop in
      if start < stop then Some (start, [Receiver_name (String.sub text start (stop - start), index_count)]) else None
    )
  and collect_chain stop acc =
    match segment_before stop with
    | Some (start, segments) ->
        let acc = segments @ acc in
        let before_start = skip_left start in
        let dot = before_start - 1 in
        if dot >= 0 && text.[dot] = '.' then collect_chain dot acc else Some (start, acc)
    | None -> None
  and if_receiver_segments content_start content_stop index_count =
    if not (text_starts_with_keyword text content_start "if") then None
    else (
      let depths = Lazy.force delimiter_depths_cache in
      let depth = depths.(content_start) in
      let branch_chain start stop =
        let start = skip_right start stop in
        let stop = skip_left stop in
        if start >= stop then None
        else (
          match collect_chain stop [] with
          | Some (chain_start, segments) when chain_start = start -> Some segments
          | _ -> None
        )
      in
      match find_top_level_keyword_offset text depths (content_start + 2) content_stop "then" depth with
      | None -> None
      | Some then_offset -> (
          match find_top_level_keyword_offset text depths (then_offset + 4) content_stop "else" depth with
          | None -> None
          | Some else_offset ->
              Option.bind
                (branch_chain (then_offset + 4) else_offset)
                (fun then_segments ->
                  Option.bind
                    (branch_chain (else_offset + 4) content_stop)
                    (fun else_segments -> Some [Receiver_if (then_segments, else_segments, index_count)])
                )
        )
    )
  in
  let collect stop =
    let before_field = skip_left stop in
    let dot = before_field - 1 in
    if dot >= 0 && text.[dot] = '.' then (
      match collect_chain dot [] with Some (_, segments) -> Some segments | None -> None
    )
    else None
  in
  collect field_start

let completion_receiver_chain_type docs text position segments =
  let rec segment_type owner_type = function
    | Receiver_name (name, index_count) -> (
        match owner_type with
        | None ->
            Option.bind (completion_name_type_in_scope text position name) (fun ty ->
                apply_receiver_indexes ty index_count
            )
        | Some ty ->
            Option.bind (struct_field_type_from_docs docs ty name) (fun field_ty ->
                apply_receiver_indexes field_ty index_count
            )
      )
    | Receiver_call (name, index_count) ->
        Option.bind (callable_return_type_from_docs docs name) (fun ty -> apply_receiver_indexes ty index_count)
    | Receiver_if (then_segments, else_segments, index_count) ->
        Option.bind (chain_type then_segments) (fun then_ty ->
            Option.bind (chain_type else_segments) (fun else_ty ->
                if completion_type_matches_owner then_ty else_ty then apply_receiver_indexes then_ty index_count
                else None
            )
        )
  and chain_type = function
    | [] -> None
    | root :: fields ->
        let root_type = segment_type None root in
        List.fold_left
          (fun owner_type segment -> Option.bind owner_type (fun ty -> segment_type (Some ty) segment))
          root_type fields
  in
  chain_type segments

let completion_extra_source_items uri text position prefix =
  let docs = workspace_documents ~current_uri:uri ~current_text:text () in
  let expected_type = completion_expected_type text position in
  let enum_items = List.concat_map (fun doc -> enum_completion_items_from_doc ?expected_type doc prefix) docs in
  let union_items = List.concat_map (fun doc -> union_completion_items_from_doc ?expected_type doc prefix) docs in
  let field_items =
    if completion_is_field_context text position prefix then (
      let receiver_type =
        Option.bind (completion_field_receiver_chain text position prefix) (fun receiver_chain ->
            completion_receiver_chain_type docs text position receiver_chain
        )
      in
      List.concat_map (fun doc -> field_completion_items_from_doc ?receiver_type doc prefix) docs
    )
    else []
  in
  enum_items @ union_items @ field_items

let completion_item_label = function
  | `Assoc fields -> (
      match List.assoc_opt "label" fields with Some (`String label) -> Some label | _ -> None
    )
  | _ -> None

let unique_completion_items items =
  let seen = Hashtbl.create 128 in
  List.filter
    (fun item ->
      match completion_item_label item with
      | None -> true
      | Some label ->
          if Hashtbl.mem seen label then false
          else (
            Hashtbl.add seen label ();
            true
          )
    )
    items

let unique_completion_entries entries =
  let table = Hashtbl.create 256 in
  entries
  |> List.sort (fun a b ->
      match compare (source_graph_preference a) (source_graph_preference b) with
      | 0 -> String.compare a.graph_name b.graph_name
      | n -> n
  )
  |> List.iter (fun entry -> if not (Hashtbl.mem table entry.graph_name) then Hashtbl.add table entry.graph_name entry);
  Hashtbl.fold (fun _ entry acc -> entry :: acc) table []
  |> List.sort (fun a b ->
      match compare (source_graph_preference a) (source_graph_preference b) with
      | 0 -> String.compare a.graph_name b.graph_name
      | n -> n
  )

let handle_completion id params =
  match (text_document_uri params, position_param params) with
  | Some uri, Some position -> (
      match document_text uri with
      | None -> response id (`Assoc [("isIncomplete", `Bool false); ("items", `List [])])
      | Some text -> (
          match completion_include_context text position with
          | Some (prefix, range) ->
              let items = include_completion_items uri prefix range in
              response id (`Assoc [("isIncomplete", `Bool false); ("items", `List items)])
          | None ->
              let prefix = completion_prefix text position in
              let local_names = completion_local_let_names text position prefix in
              let match_arm_names = completion_match_arm_names text position prefix in
              let mapping_names = completion_mapping_names text position prefix in
              let loop_names = completion_loop_names text position prefix in
              let parameter_names = completion_parameter_names text position prefix in
              let function_pattern_names = completion_function_pattern_names text position prefix in
              let local_items = List.map completion_local_item_json local_names in
              let match_arm_items = List.map completion_pattern_item_json match_arm_names in
              let mapping_items = List.map completion_mapping_item_json mapping_names in
              let loop_items = List.map completion_loop_item_json loop_names in
              let parameter_items = List.map completion_parameter_item_json parameter_names in
              let function_pattern_items = List.map completion_pattern_item_json function_pattern_names in
              let extra_source_items = completion_extra_source_items uri text position prefix in
              let keyword_items =
                sail_keywords
                |> List.filter (fun keyword -> lowercase_starts_with keyword prefix)
                |> List.map completion_keyword_item_json
              in
              let entries =
                source_graph ~current_uri:uri ~current_text:text ()
                |> List.filter (fun entry ->
                    lowercase_starts_with entry.graph_name prefix
                    && not
                         (List.mem entry.graph_name
                            (local_names @ match_arm_names @ mapping_names @ loop_names @ parameter_names
                           @ function_pattern_names
                            )
                         )
                )
                |> unique_completion_entries |> List.map completion_item_json
              in
              let items =
                unique_completion_items
                  (local_items @ match_arm_items @ mapping_items @ loop_items @ parameter_items @ function_pattern_items
                 @ extra_source_items @ entries @ keyword_items
                  )
              in
              response id (`Assoc [("isIncomplete", `Bool false); ("items", `List items)])
        )
    )
  | _ -> response id (`Assoc [("isIncomplete", `Bool false); ("items", `List [])])

let handle_document_symbol id params =
  match text_document_uri params with
  | None -> response id `Null
  | Some uri -> (
      match document_text uri with
      | None -> response id (`List [])
      | Some text -> response id (`List (List.map symbol_json (document_symbols uri text)))
    )

let handle_semantic_tokens id params =
  match text_document_uri params with
  | None -> response id (`Assoc [("data", `List [])])
  | Some uri -> (
      match document_text uri with
      | None -> response id (`Assoc [("data", `List [])])
      | Some text ->
          response id (`Assoc [("data", `List (encode_semantic_tokens (graph_semantic_tokens_with_workspace uri text)))])
    )

let c_location_json target =
  match generated_c_location target with
  | Some (uri, range) -> `Assoc [("uri", `String uri); ("range", json_range range)]
  | None -> `Null

let c_name_response target =
  let fields =
    [
      ("cName", `String target.c_name);
      ("cLocation", c_location_json target);
      ("cFiles", `List (List.map (fun path -> `String path) target.c_files));
      ("source", `String target.source);
    ]
  in
  let fields = match target.sail_name with Some name -> ("sailName", `String name) :: fields | None -> fields in
  let fields = match target.kind with Some kind -> ("kind", `String kind) :: fields | None -> fields in
  let fields =
    match target.generated with Some generated -> ("generated", `Bool generated) :: fields | None -> fields
  in
  let fields =
    match target.fallback_reason with Some reason -> ("fallbackReason", `String reason) :: fields | None -> fields
  in
  `Assoc fields

let handle_c_name id params =
  match (text_document_uri params, position_param params) with
  | Some uri, Some position -> (
      match Option.bind (document_text uri) (fun text -> generated_c_target_at_position text position) with
      | Some target -> response id (c_name_response target)
      | None -> response id `Null
    )
  | _ -> response id `Null

let handle_generated_c id params =
  match (text_document_uri params, position_param params) with
  | Some uri, Some position -> (
      match Option.bind (document_text uri) (fun text -> generated_c_target_at_position text position) with
      | Some target -> (
          match generated_c_location target with
          | Some (c_uri, c_range) -> response id (location_json c_uri c_range)
          | None -> response id `Null
        )
      | None -> response id `Null
    )
  | _ -> response id `Null

let handle_documentation id params =
  match (text_document_uri params, position_param params) with
  | Some uri, Some position -> (
      match document_text uri with
      | None -> response id `Null
      | Some text -> (
          match Option.bind (word_at_position text position) (find_documentation_entry uri text) with
          | Some entry -> response id (doc_entry_json entry)
          | None -> response id `Null
        )
    )
  | _ -> response id `Null

let type_entry_json entry =
  `Assoc
    [
      ("name", `String entry.doc_name);
      ("kind", `String entry.doc_kind);
      ("type", doc_entry_type_json entry);
      ("location", doc_location_json entry.doc_location);
      ("docinfo", `String entry.doc_path);
    ]

let type_json_has_type = function
  | `Assoc fields -> (
      match List.assoc_opt "type" fields with Some (`String _) -> true | _ -> false
    )
  | _ -> false

let type_info_at_position uri text position =
  match word_at_position text position with
  | None -> Option.map compiler_type_entry_json (compiler_type_entry_at_position uri text position)
  | Some name -> (
      match compiler_type_entry_for_name uri text name with
      | Some entry -> Some (compiler_type_entry_json entry)
      | None -> (
          match compiler_type_entry_at_position uri text position with
          | Some entry -> Some (compiler_type_entry_json entry)
          | None -> (
              match find_docinfo_entry name with
              | Some entry when Option.is_some (doc_entry_type entry) -> Some (type_entry_json entry)
              | Some entry -> (
                  match source_type_entry_for_name uri text name with
                  | Some source_entry -> Some (source_type_entry_json source_entry)
                  | None -> Some (type_entry_json entry)
                )
              | None -> Option.map source_type_entry_json (source_type_entry_for_name uri text name)
            )
        )
    )

let handle_type_at_cursor id params =
  match (text_document_uri params, position_param params) with
  | Some uri, Some position -> (
      match Option.bind (document_text uri) (fun text -> type_info_at_position uri text position) with
      | Some type_info -> response id type_info
      | None -> response id `Null
    )
  | _ -> response id `Null

let c_hover_markdown target =
  match (target.source, generated_c_location target) with
  | "zencodeFallback", None -> None
  | _, location ->
      let sail_line = match target.sail_name with Some name -> [Printf.sprintf "**Sail** `%s`" name] | None -> [] in
      let location_line =
        match location with Some (c_uri, _) -> [Printf.sprintf "Location: `%s`" c_uri] | None -> []
      in
      Some
        (String.concat "\n\n"
           (sail_line
           @ [Printf.sprintf "**Generated C** `%s`" target.c_name; Printf.sprintf "Mapping source: `%s`" target.source]
           @ location_line
           )
        )

let handle_hover id params =
  match (text_document_uri params, position_param params) with
  | Some uri, Some position -> (
      match document_text uri with
      | None -> response id `Null
      | Some text -> (
          let doc_markdown =
            match word_at_position text position with
            | Some name -> Option.map (fun entry -> entry.doc_markdown) (find_documentation_entry uri text name)
            | None -> None
          in
          let type_markdown =
            match doc_markdown with
            | Some _ -> None
            | None -> (
                match type_info_at_position uri text position with
                | Some (`Assoc fields) -> (
                    match
                      (List.assoc_opt "name" fields, List.assoc_opt "kind" fields, List.assoc_opt "type" fields)
                    with
                    | Some (`String name), Some (`String kind), Some (`String ty) ->
                        Some (Printf.sprintf "**Sail %s** `%s`\n\n```sail\n%s\n```" kind name ty)
                    | _ -> None
                  )
                | _ -> None
              )
          in
          let c_markdown = Option.bind (generated_c_target_at_position text position) c_hover_markdown in
          let parts = List.filter_map Fun.id [doc_markdown; type_markdown; c_markdown] in
          match parts with
          | [] -> response id `Null
          | _ ->
              let value = String.concat "\n\n---\n\n" parts in
              response id (`Assoc [("contents", `Assoc [("kind", `String "markdown"); ("value", `String value)])])
        )
    )
  | _ -> response id `Null

let same_position a b = a.line = b.line && a.character = b.character

let same_range a b = same_position a.start_pos b.start_pos && same_position a.end_pos b.end_pos

let position_less_equal a b = a.line < b.line || (a.line = b.line && a.character <= b.character)

let position_in_range position range =
  position_less_equal range.start_pos position && position_less_equal position range.end_pos

let references_include_declaration params =
  match json_member "context" params with
  | Some context -> json_bool_member "includeDeclaration" context |> Option.value ~default:true
  | None -> true

let declaration_reference_ranges (docs : workspace_document list) name =
  docs
  |> List.concat_map (fun (doc : workspace_document) ->
      document_symbols doc.doc_uri doc.doc_text
      |> List.filter (fun symbol -> symbol.name = name)
      |> List.map (fun symbol -> { loc_uri = symbol.uri; loc_range = symbol.selection_range })
  )

let is_declaration_reference declarations reference =
  List.exists
    (fun declaration -> declaration.loc_uri = reference.loc_uri && same_range declaration.loc_range reference.loc_range)
    declarations

let line_is_top_level text line_no =
  match line_at text line_no with Some line when String.trim line <> "" -> not (is_space line.[0]) | _ -> false

let top_level_document_symbols uri text =
  document_symbols uri text |> List.filter (fun symbol -> line_is_top_level text symbol.range.start_pos.line)

let range_contains_range outer inner =
  position_less_equal outer.start_pos inner.start_pos && position_less_equal inner.end_pos outer.end_pos

let end_position_of_text text =
  let lines = lines_of_text text in
  let last_line_no = max 0 (List.length lines - 1) in
  let last_line = List.nth lines last_line_no in
  { line = last_line_no; character = String.length last_line }

let enclosing_top_level_range uri text position =
  let symbols =
    top_level_document_symbols uri text
    |> List.sort (fun a b ->
        match compare a.range.start_pos.line b.range.start_pos.line with
        | 0 -> compare a.range.start_pos.character b.range.start_pos.character
        | n -> n
    )
  in
  let rec loop current = function
    | [] -> (
        match current with
        | Some symbol -> Some { start_pos = symbol.range.start_pos; end_pos = end_position_of_text text }
        | None -> None
      )
    | symbol :: rest ->
        if position_less_equal symbol.range.start_pos position then loop (Some symbol) rest
        else (
          match current with
          | Some current -> Some { start_pos = current.range.start_pos; end_pos = symbol.range.start_pos }
          | None -> Some { start_pos = { line = 0; character = 0 }; end_pos = symbol.range.start_pos }
        )
  in
  loop None symbols

let local_reference_ranges uri text position name =
  match compiler_lvar_kind_at_position uri text position name with
  | Some Compiler_local -> (
      let doc = { doc_uri = uri; doc_path = path_of_uri uri; doc_text = text } in
      match enclosing_top_level_range uri text position with
      | Some scope ->
          Some
            (reference_ranges_in_document doc name
            |> List.filter (fun reference -> range_contains_range scope reference.loc_range)
            )
      | None -> Some (reference_ranges_in_document doc name)
    )
  | _ -> None

let function_header_definition_ranges uri text position name kind =
  let line_no = completion_scope_start_line text position in
  match line_at text line_no with
  | None -> []
  | Some line ->
      function_header_binding_tokens_from_line line
      |> List.filter_map (fun binding ->
          if binding.function_header_binding_name = name && binding.function_header_binding_kind = kind then
            Some
              {
                loc_uri = uri;
                loc_range =
                  {
                    start_pos = { line = line_no; character = binding.function_header_binding_start };
                    end_pos = { line = line_no; character = binding.function_header_binding_stop };
                  };
              }
          else None
      )

let parameter_definition_ranges uri text position name =
  function_header_definition_ranges uri text position name Parameter_binding

let function_pattern_definition_ranges uri text position name =
  function_header_definition_ranges uri text position name Function_pattern_binding

let local_let_definition_ranges uri text position name =
  let lines = lines_of_text text in
  let start_line = completion_scope_start_line text position in
  let line_prefix line_no line =
    if line_no = position.line then String.sub line 0 (min position.character (String.length line)) else line
  in
  let binding_range line_no start stop =
    {
      loc_uri = uri;
      loc_range = { start_pos = { line = line_no; character = start }; end_pos = { line = line_no; character = stop } };
    }
  in
  let rec loop line_no acc =
    if line_no > position.line then List.rev acc
    else (
      let acc =
        match List.nth_opt lines line_no with
        | Some line when line_no > start_line && line <> "" && is_space line.[0] ->
            local_let_binding_tokens_from_line (line_prefix line_no line)
            |> List.fold_left
                 (fun acc (candidate, start, stop) ->
                   if candidate = name then binding_range line_no start stop :: acc else acc
                 )
                 acc
        | _ -> acc
      in
      loop (line_no + 1) acc
    )
  in
  loop start_line []

let match_arm_definition_ranges uri text position name =
  match_arm_binding_tokens_in_scope text position
  |> List.filter_map (fun (candidate, line_no, start, stop) ->
      if candidate = name then
        Some
          {
            loc_uri = uri;
            loc_range =
              { start_pos = { line = line_no; character = start }; end_pos = { line = line_no; character = stop } };
          }
      else None
  )

let mapping_definition_ranges uri text position name =
  mapping_binding_tokens_in_scope text position
  |> List.filter_map (fun (candidate, line_no, start, stop) ->
      if candidate = name then
        Some
          {
            loc_uri = uri;
            loc_range =
              { start_pos = { line = line_no; character = start }; end_pos = { line = line_no; character = stop } };
          }
      else None
  )

let loop_definition_ranges uri text position name =
  loop_binding_tokens_in_scope text position
  |> List.filter_map (fun (candidate, line_no, start, stop) ->
      if candidate = name then
        Some
          {
            loc_uri = uri;
            loc_range =
              { start_pos = { line = line_no; character = start }; end_pos = { line = line_no; character = stop } };
          }
      else None
  )

let latest_definition_before position definitions =
  definitions
  |> List.filter (fun definition -> position_less_equal definition.loc_range.start_pos position)
  |> List.sort (fun a b -> compare b.loc_range.start_pos a.loc_range.start_pos)
  |> function
  | definition :: _ -> Some definition
  | [] -> None

let local_definition_location uri text position name =
  parameter_definition_ranges uri text position name
  @ function_pattern_definition_ranges uri text position name
  @ local_let_definition_ranges uri text position name
  @ match_arm_definition_ranges uri text position name
  @ mapping_definition_ranges uri text position name
  @ loop_definition_ranges uri text position name
  |> latest_definition_before position

let document_for_reference (docs : workspace_document list) reference =
  List.find_opt (fun (doc : workspace_document) -> doc.doc_uri = reference.loc_uri) docs

let reference_is_local_let_binding (doc : workspace_document) reference =
  let line_no = reference.loc_range.start_pos.line in
  if line_is_top_level doc.doc_text line_no then false
  else (
    match line_at doc.doc_text line_no with
    | None -> false
    | Some line ->
        local_let_binding_tokens_from_line line
        |> List.exists (fun (_, start, stop) ->
            start = reference.loc_range.start_pos.character && stop = reference.loc_range.end_pos.character
        )
  )

let local_let_binding_references (doc : workspace_document) name =
  reference_ranges_in_document doc name |> List.filter (reference_is_local_let_binding doc)

let reference_is_match_arm_binding (doc : workspace_document) reference =
  let reference_start = offset_of_position doc.doc_text reference.loc_range.start_pos in
  let reference_stop = offset_of_position doc.doc_text reference.loc_range.end_pos in
  match_arm_binding_tokens_from_text doc.doc_text
  |> List.exists (fun binding ->
      binding.match_arm_binding_start = reference_start && binding.match_arm_binding_stop = reference_stop
  )

let reference_is_mapping_binding (doc : workspace_document) reference =
  let reference_start = offset_of_position doc.doc_text reference.loc_range.start_pos in
  let reference_stop = offset_of_position doc.doc_text reference.loc_range.end_pos in
  mapping_binding_tokens_from_text doc.doc_text
  |> List.exists (fun binding ->
      binding.mapping_binding_start = reference_start && binding.mapping_binding_stop = reference_stop
  )

let reference_is_loop_binding (doc : workspace_document) reference =
  let reference_start = offset_of_position doc.doc_text reference.loc_range.start_pos in
  let reference_stop = offset_of_position doc.doc_text reference.loc_range.end_pos in
  foreach_loop_bindings_from_text doc.doc_text
  |> List.exists (fun binding ->
      binding.loop_binding_start = reference_start && binding.loop_binding_stop = reference_stop
  )

let reference_is_function_header_binding (doc : workspace_document) reference =
  match line_at doc.doc_text reference.loc_range.start_pos.line with
  | None -> false
  | Some line ->
      function_header_binding_tokens_from_line line
      |> List.exists (fun binding ->
          binding.function_header_binding_start = reference.loc_range.start_pos.character
          && binding.function_header_binding_stop = reference.loc_range.end_pos.character
      )

let function_header_binding_tokens_in_scope text position =
  let line_no = completion_scope_start_line text position in
  match line_at text line_no with
  | None -> []
  | Some line ->
      function_header_binding_tokens_from_line line
      |> List.map (fun binding ->
          ( binding.function_header_binding_name,
            line_no,
            binding.function_header_binding_start,
            binding.function_header_binding_stop
          )
      )

let reference_is_shadowed_by_local_let (doc : workspace_document) name reference =
  local_let_binding_references doc name
  |> List.exists (fun binding ->
      position_less_equal binding.loc_range.start_pos reference.loc_range.start_pos
      &&
      match enclosing_top_level_range doc.doc_uri doc.doc_text binding.loc_range.start_pos with
      | Some scope -> range_contains_range scope reference.loc_range
      | None -> false
  )

let reference_is_shadowed_by_match_arm (doc : workspace_document) name reference =
  match_arm_binding_tokens_in_scope doc.doc_text reference.loc_range.start_pos
  |> List.exists (fun (candidate, _, _, _) -> candidate = name)

let reference_is_shadowed_by_mapping (doc : workspace_document) name reference =
  mapping_binding_tokens_in_scope doc.doc_text reference.loc_range.start_pos
  |> List.exists (fun (candidate, _, _, _) -> candidate = name)

let reference_is_shadowed_by_loop (doc : workspace_document) name reference =
  loop_binding_tokens_in_scope doc.doc_text reference.loc_range.start_pos
  |> List.exists (fun (candidate, _, _, _) -> candidate = name)

let reference_is_shadowed_by_function_header (doc : workspace_document) name reference =
  function_header_binding_tokens_in_scope doc.doc_text reference.loc_range.start_pos
  |> List.exists (fun (candidate, _, _, _) -> candidate = name)

let reference_is_compiler_local docs name reference =
  match document_for_reference docs reference with
  | None -> false
  | Some doc -> (
      match compiler_lvar_kind_at_position doc.doc_uri doc.doc_text reference.loc_range.start_pos name with
      | Some Compiler_local -> true
      | _ ->
          reference_is_local_let_binding doc reference
          || reference_is_shadowed_by_local_let doc name reference
          || reference_is_match_arm_binding doc reference
          || reference_is_shadowed_by_match_arm doc name reference
          || reference_is_mapping_binding doc reference
          || reference_is_shadowed_by_mapping doc name reference
          || reference_is_loop_binding doc reference
          || reference_is_shadowed_by_loop doc name reference
          || reference_is_function_header_binding doc reference
          || reference_is_shadowed_by_function_header doc name reference
    )

let global_reference_ranges docs name refs =
  let filtered = List.filter (fun reference -> not (reference_is_compiler_local docs name reference)) refs in
  match filtered with [] -> refs | _ -> filtered

let handle_references id params =
  match (text_document_uri params, position_param params) with
  | Some uri, Some position -> (
      match document_text uri with
      | None -> response id (`List [])
      | Some text -> (
          match word_at_position text position with
          | None -> response id (`List [])
          | Some name ->
              let docs = workspace_documents ~current_uri:uri ~current_text:text () in
              let refs =
                match local_reference_ranges uri text position name with
                | Some refs -> refs
                | None -> (
                    match source_graph_reference_ranges uri text name with
                    | Some (_ :: _ as refs) -> global_reference_ranges docs name refs
                    | _ ->
                        docs
                        |> List.concat_map (fun doc -> reference_ranges_in_document doc name)
                        |> global_reference_ranges docs name
                  )
              in
              let refs =
                if references_include_declaration params then refs
                else (
                  let declarations = declaration_reference_ranges docs name in
                  List.filter (fun reference -> not (is_declaration_reference declarations reference)) refs
                )
              in
              response id (`List (List.map (fun reference -> location_json reference.loc_uri reference.loc_range) refs))
        )
    )
  | _ -> response id (`List [])

let document_highlight_json reference = `Assoc [("range", json_range reference.loc_range); ("kind", `Int 1)]

let document_highlight_ranges uri text position name =
  let refs =
    match local_reference_ranges uri text position name with
    | Some refs -> refs
    | None -> (
        let docs = workspace_documents ~current_uri:uri ~current_text:text () in
        match source_graph_reference_ranges uri text name with
        | Some (_ :: _ as refs) -> global_reference_ranges docs name refs
        | _ ->
            reference_ranges_in_document { doc_uri = uri; doc_path = path_of_uri uri; doc_text = text } name
            |> global_reference_ranges docs name
      )
  in
  refs |> List.filter (fun reference -> reference.loc_uri = uri)

let handle_document_highlight id params =
  match (text_document_uri params, position_param params) with
  | Some uri, Some position -> (
      match document_text uri with
      | None -> response id (`List [])
      | Some text -> (
          match word_at_position text position with
          | None -> response id (`List [])
          | Some name ->
              response id (`List (List.map document_highlight_json (document_highlight_ranges uri text position name)))
        )
    )
  | _ -> response id (`List [])

let cursor_params_json uri position =
  `Assoc [("textDocument", `Assoc [("uri", `String uri)]); ("position", json_position position)]

let command_json title command arguments =
  `Assoc [("title", `String title); ("command", `String command); ("arguments", `List arguments)]

let code_action_json title kind command arguments =
  `Assoc [("title", `String title); ("kind", `String kind); ("command", command_json title command arguments)]

let workspace_edit_json uri edits = `Assoc [("changes", `Assoc [(uri, `List edits)])]

let code_action_edit_json title kind edit = `Assoc [("title", `String title); ("kind", `String kind); ("edit", edit)]

let code_lens_json range command = `Assoc [("range", json_range range); ("command", command)]

let diagnostic_codes_from_params params =
  match json_member "context" params with
  | Some context -> (
      match json_list_member "diagnostics" context with
      | Some diagnostics ->
          diagnostics
          |> List.filter_map (fun diagnostic ->
              match json_member "code" diagnostic with
              | Some (`String code) -> Some code
              | Some (`Int code) -> Some (string_of_int code)
              | _ -> None
          )
      | None -> []
    )
  | None -> []

let handle_document_link id params =
  match text_document_uri params with
  | None -> response id (`List [])
  | Some uri -> (
      match document_text uri with
      | None -> response id (`List [])
      | Some text ->
          let links =
            string_literals_in_text text
            |> List.filter_map (fun literal ->
                if is_c_annotation_value text literal then (
                  match find_c_location literal.value with
                  | Some (c_uri, _) ->
                      Some
                        (`Assoc
                           [
                             ( "range",
                               json_range
                                 {
                                   start_pos = position_of_offset text literal.value_start;
                                   end_pos = position_of_offset text literal.value_stop;
                                 }
                             );
                             ("target", `String c_uri);
                             ("tooltip", `String ("Go to generated C symbol " ^ literal.value));
                           ]
                        )
                  | None -> None
                )
                else None
            )
          in
          let doc_links =
            document_symbols uri text
            |> List.filter_map (fun symbol ->
                match find_docinfo_entry symbol.name with
                | Some { doc_url = Some url; _ } ->
                    Some
                      (`Assoc
                         [
                           ("range", json_range symbol.selection_range);
                           ("target", `String url);
                           ("tooltip", `String ("Open generated documentation for " ^ symbol.name));
                         ]
                      )
                | _ -> None
            )
          in
          response id (`List (links @ doc_links))
    )

let handle_code_lens id params =
  match text_document_uri params with
  | None -> response id (`List [])
  | Some uri -> (
      match document_text uri with
      | None -> response id (`List [])
      | Some text ->
          let lenses =
            document_symbols uri text
            |> List.concat_map (fun symbol ->
                let position = symbol.selection_range.start_pos in
                let cursor_params = cursor_params_json uri position in
                let generated_c_lenses =
                  match generated_c_target_at_position text position with
                  | Some target when Option.is_some (generated_c_location target) ->
                      [
                        code_lens_json symbol.selection_range
                          (command_json "Go to Generated C" "sail.goToGeneratedC" [cursor_params]);
                      ]
                  | _ -> []
                in
                let docinfo = find_documentation_entry uri text symbol.name in
                let has_type =
                  match docinfo with
                  | Some entry -> Option.is_some (doc_entry_type entry)
                  | None -> Option.is_some (source_type_entry_for_name uri text symbol.name)
                in
                let type_lenses =
                  if has_type then
                    [code_lens_json symbol.selection_range (command_json "Show Type" "sail.showType" [cursor_params])]
                  else []
                in
                let documentation_lenses =
                  match docinfo with
                  | Some _ ->
                      [
                        code_lens_json symbol.selection_range
                          (command_json "Show Documentation" "sail.showDocumentation" [cursor_params]);
                      ]
                  | None -> []
                in
                generated_c_lenses @ type_lenses @ documentation_lenses
            )
          in
          response id (`List lenses)
    )

let symbol_at_position uri text position =
  document_symbols uri text |> List.find_opt (fun symbol -> position_in_range position symbol.selection_range)

let previous_nonempty_line lines line_no =
  let rec loop i =
    if i < 0 then None
    else (
      match List.nth_opt lines i with
      | Some line when String.trim line <> "" -> Some (String.trim line)
      | _ -> loop (i - 1)
    )
  in
  loop (line_no - 1)

let has_c_annotation_before_line text line_no =
  match previous_nonempty_line (lines_of_text text) line_no with
  | Some line -> starts_with ~prefix:"$[" line && lowercase_ascii_contains line "c:"
  | None -> false

let c_annotation_code_action uri text position =
  match symbol_at_position uri text position with
  | None -> None
  | Some symbol -> (
      match generated_c_target_at_position text symbol.selection_range.start_pos with
      | Some target when not (has_c_annotation_before_line text symbol.selection_range.start_pos.line) ->
          let annotation = Printf.sprintf "$[c: \"%s\"]\n" (String.escaped target.c_name) in
          let insert_position = { line = symbol.range.start_pos.line; character = 0 } in
          let edit = text_edit_json { start_pos = insert_position; end_pos = insert_position } annotation in
          Some (code_action_edit_json "Sail: Insert C Annotation" "quickfix" (workspace_edit_json uri [edit]))
      | _ -> None
    )

let has_val_spec uri text name =
  workspace_documents ~current_uri:uri ~current_text:text ()
  |> List.exists (fun (doc : workspace_document) ->
      document_symbols doc.doc_uri doc.doc_text
      |> List.exists (fun symbol -> symbol.name = name && symbol.detail = "val")
  )

let no_arg_function_symbol text symbol =
  symbol.detail = "function"
  &&
  match symbol_source_line text symbol with
  | None -> false
  | Some line ->
      let after_name_start = min (String.length line) symbol.selection_range.end_pos.character in
      let after_name = String.sub line after_name_start (String.length line - after_name_start) |> String.trim in
      starts_with ~prefix:"()" after_name

let val_spec_code_action uri text position =
  match symbol_at_position uri text position with
  | Some symbol when no_arg_function_symbol text symbol && not (has_val_spec uri text symbol.name) ->
      let insert_position = { line = symbol.range.start_pos.line; character = 0 } in
      let new_text = Printf.sprintf "val %s : unit -> unit\n\n" symbol.name in
      let edit = text_edit_json { start_pos = insert_position; end_pos = insert_position } new_text in
      Some (code_action_edit_json "Sail: Insert Val Spec" "quickfix" (workspace_edit_json uri [edit]))
  | _ -> None

let has_default_order text =
  lines_of_text text
  |> List.exists (fun line ->
      match tokens_from line 0 with ("default", _, _) :: ("Order", _, _) :: _ -> true | _ -> false
  )

let default_order_code_action uri text diagnostic_codes =
  if List.mem "sail.order.default" diagnostic_codes && not (has_default_order text) then (
    let start = { line = 0; character = 0 } in
    let edit = text_edit_json { start_pos = start; end_pos = start } "default Order dec\n\n" in
    Some (code_action_edit_json "Sail: Insert Default Order" "quickfix" (workspace_edit_json uri [edit]))
  )
  else None

let unbound_val_spec_code_action uri text position diagnostic_codes =
  if List.mem "sail.name.unbound" diagnostic_codes then (
    match word_at_position text position with
    | Some name when not (has_val_spec uri text name) ->
        let start = { line = 0; character = 0 } in
        let edit =
          text_edit_json { start_pos = start; end_pos = start } (Printf.sprintf "val %s : unit -> unit\n\n" name)
        in
        Some (code_action_edit_json "Sail: Insert Val Spec Stub" "quickfix" (workspace_edit_json uri [edit]))
    | _ -> None
  )
  else None

let identifiers_on_line line =
  let len = String.length line in
  let rec scan i acc =
    if i >= len then List.rev acc
    else if is_ident_char line.[i] then (
      let rec take j = if j < len && is_ident_char line.[j] then take (j + 1) else j in
      let stop = take (i + 1) in
      let word = String.sub line i (stop - i) in
      scan stop ((word, i, stop) :: acc)
    )
    else scan (i + 1) acc
  in
  scan 0 []

let text_has_identifier text name =
  lines_of_text text
  |> List.exists (fun line -> identifiers_on_line line |> List.exists (fun (word, _, _) -> word = name))

let duplicate_identifier_occurrence line position =
  let identifiers = identifiers_on_line line in
  let cursor = min position.character (String.length line) in
  let earlier_same name start =
    identifiers |> List.exists (fun (other, other_start, _) -> other = name && other_start < start)
  in
  match identifiers |> List.find_opt (fun (_, start, stop) -> start <= cursor && cursor <= stop) with
  | Some (name, start, stop) when earlier_same name start -> Some (name, start, stop)
  | _ ->
      let seen = Hashtbl.create 8 in
      identifiers
      |> List.find_map (fun (name, start, stop) ->
          if Hashtbl.mem seen name then Some (name, start, stop)
          else (
            Hashtbl.add seen name ();
            None
          )
      )

let fresh_duplicate_binding_name text name =
  let rec loop suffix =
    let candidate = name ^ "_" ^ string_of_int suffix in
    if text_has_identifier text candidate then loop (suffix + 1) else candidate
  in
  loop 2

let duplicate_binding_code_action uri text position diagnostic_codes =
  if List.mem "sail.name.duplicateBinding" diagnostic_codes then (
    match line_at text position.line with
    | Some line -> (
        match duplicate_identifier_occurrence line position with
        | Some (name, start, stop) ->
            let new_name = fresh_duplicate_binding_name text name in
            let edit =
              text_edit_json
                {
                  start_pos = { line = position.line; character = start };
                  end_pos = { line = position.line; character = stop };
                }
                new_name
            in
            Some (code_action_edit_json "Sail: Rename Duplicate Binding" "quickfix" (workspace_edit_json uri [edit]))
        | None -> None
      )
    | None -> None
  )
  else None

let handle_code_action id params =
  match (text_document_uri params, range_start_param params) with
  | Some uri, Some position -> (
      match document_text uri with
      | None -> response id (`List [])
      | Some text ->
          let cursor_params = cursor_params_json uri position in
          let generated_c_actions =
            match generated_c_target_at_position text position with
            | None -> []
            | Some target ->
                let c_name_action =
                  code_action_json "Sail: Show Generated C Name" "quickfix" "sail.showCName" [cursor_params]
                in
                let go_to_action =
                  match generated_c_location target with
                  | Some _ ->
                      [code_action_json "Sail: Go to Generated C" "quickfix" "sail.goToGeneratedC" [cursor_params]]
                  | None -> []
                in
                c_name_action :: go_to_action
          in
          let documentation_actions =
            let type_actions =
              match type_info_at_position uri text position with
              | Some type_info when type_json_has_type type_info ->
                  [code_action_json "Sail: Show Type" "quickfix" "sail.showType" [cursor_params]]
              | _ -> []
            in
            let doc_actions =
              match Option.bind (word_at_position text position) (find_documentation_entry uri text) with
              | Some _ ->
                  [code_action_json "Sail: Show Documentation" "quickfix" "sail.showDocumentation" [cursor_params]]
              | None -> []
            in
            type_actions @ doc_actions
          in
          let check_action =
            code_action_json "Sail: Check Current File" "source" "sail.checkCurrentFile"
              [`Assoc [("textDocument", `Assoc [("uri", `String uri)])]]
          in
          let project_actions =
            if List.mem "sail.project.ambiguous" (diagnostic_codes_from_params params) then
              [code_action_json "Sail: Choose Project File" "quickfix" "sail.chooseProjectFile" []]
            else []
          in
          let diagnostic_codes = diagnostic_codes_from_params params in
          let edit_actions =
            List.filter_map Fun.id
              [
                c_annotation_code_action uri text position;
                val_spec_code_action uri text position;
                default_order_code_action uri text diagnostic_codes;
                unbound_val_spec_code_action uri text position diagnostic_codes;
                duplicate_binding_code_action uri text position diagnostic_codes;
              ]
          in
          response id
            (`List (generated_c_actions @ documentation_actions @ project_actions @ edit_actions @ [check_action]))
    )
  | _ -> response id (`List [])

let handle_definition id params =
  match (text_document_uri params, position_param params) with
  | Some uri, Some position -> (
      match document_text uri with
      | None -> response id `Null
      | Some text -> (
          match c_annotation_at_position text position with
          | Some (c_name, _) -> (
              match find_c_location c_name with
              | Some (c_uri, c_range) -> response id (location_json c_uri c_range)
              | None -> response id `Null
            )
          | None -> (
              match word_at_position text position with
              | None -> response id `Null
              | Some name -> (
                  match local_definition_location uri text position name with
                  | Some location -> response id (location_json location.loc_uri location.loc_range)
                  | None -> (
                      match source_graph_symbol_location uri text name with
                      | Some (sail_uri, sail_range) -> response id (location_json sail_uri sail_range)
                      | None -> (
                          match find_docinfo_entry name with
                          | Some { doc_location = Some location; _ } ->
                              response id (location_json location.doc_uri location.doc_range)
                          | _ -> response id `Null
                        )
                    )
                )
            )
        )
    )
  | _ -> response id `Null

let initialize_result =
  `Assoc
    [
      ("serverInfo", `Assoc [("name", `String "sail_lsp"); ("version", `String "0.1.0")]);
      ( "capabilities",
        `Assoc
          [
            ("textDocumentSync", `Assoc [("openClose", `Bool true); ("change", `Int 1); ("save", `Assoc [])]);
            ("definitionProvider", `Bool true);
            ("referencesProvider", `Bool true);
            ("documentHighlightProvider", `Bool true);
            ("documentSymbolProvider", `Bool true);
            ("workspaceSymbolProvider", `Bool true);
            ( "completionProvider",
              `Assoc
                [
                  ("resolveProvider", `Bool false);
                  ( "triggerCharacters",
                    `List [`String "_"; `String "'"; `String "#"; `String "<"; `String "\""; `String "/"; `String "."]
                  );
                ]
            );
            ("hoverProvider", `Bool true);
            ("documentFormattingProvider", `Bool true);
            ("documentLinkProvider", `Assoc [("resolveProvider", `Bool false)]);
            ("codeLensProvider", `Assoc [("resolveProvider", `Bool false)]);
            ("codeActionProvider", `Assoc [("codeActionKinds", `List [`String "quickfix"; `String "source"])]);
            ( "semanticTokensProvider",
              `Assoc
                [
                  ( "legend",
                    `Assoc
                      [
                        ("tokenTypes", `List (List.map (fun token_type -> `String token_type) semantic_token_types));
                        ("tokenModifiers", `List []);
                      ]
                  );
                  ("full", `Bool true);
                ]
            );
            ( "executeCommandProvider",
              `Assoc
                [
                  ( "commands",
                    `List
                      [
                        `String "sail.goToGeneratedC";
                        `String "sail.cName";
                        `String "sail.showCName";
                        `String "sail.showType";
                        `String "sail.showDocumentation";
                        `String "sail.checkCurrentFile";
                      ]
                  );
                ]
            );
          ]
      );
    ]

let handle_execute_command id params =
  match json_string_member "command" params with
  | Some "sail.showCName" -> (
      match json_list_member "arguments" params with
      | Some [params] -> (
          match (text_document_uri params, position_param params) with
          | Some uri, Some position -> (
              match Option.bind (document_text uri) (fun text -> generated_c_target_at_position text position) with
              | Some target ->
                  let prefix = match target.sail_name with Some name -> name ^ " -> " | None -> "" in
                  show_message (prefix ^ target.c_name);
                  response id `Null
              | None -> response id `Null
            )
          | _ -> response id `Null
        )
      | _ -> response id `Null
    )
  | Some "sail.cName" -> (
      match json_list_member "arguments" params with Some [params] -> handle_c_name id params | _ -> response id `Null
    )
  | Some "sail.showDocumentation" -> (
      match json_list_member "arguments" params with
      | Some [params] -> (
          match (text_document_uri params, position_param params) with
          | Some uri, Some position -> (
              match
                Option.bind (document_text uri) (fun text ->
                    Option.bind (word_at_position text position) (find_documentation_entry uri text)
                )
              with
              | Some entry ->
                  show_message entry.doc_markdown;
                  response id `Null
              | None -> response id `Null
            )
          | _ -> response id `Null
        )
      | _ -> response id `Null
    )
  | Some "sail.showType" -> (
      match json_list_member "arguments" params with
      | Some [params] -> (
          match (text_document_uri params, position_param params) with
          | Some uri, Some position -> (
              match Option.bind (document_text uri) (fun text -> type_info_at_position uri text position) with
              | Some (`Assoc fields) ->
                  let name =
                    match List.assoc_opt "name" fields with Some (`String name) -> name | _ -> "identifier"
                  in
                  let ty =
                    match List.assoc_opt "type" fields with Some (`String ty) -> ty | _ -> "No type metadata found."
                  in
                  show_message (name ^ ": " ^ ty);
                  response id `Null
              | None -> response id `Null
              | Some _ -> response id `Null
            )
          | _ -> response id `Null
        )
      | _ -> response id `Null
    )
  | Some "sail.checkCurrentFile" -> (
      match json_list_member "arguments" params with
      | Some [params] -> (
          match text_document_uri params with
          | Some uri ->
              run_diagnostics_for_uri uri;
              response id `Null
          | None -> response id `Null
        )
      | _ -> response id `Null
    )
  | Some "sail.goToGeneratedC" -> (
      match json_list_member "arguments" params with
      | Some [params] -> handle_generated_c id params
      | _ -> response id `Null
    )
  | Some command -> error_response id (-32601) ("Unknown command: " ^ command)
  | None -> error_response id (-32602) "Missing command"

let handle_request id method_ params =
  match method_ with
  | "initialize" ->
      configure_from_initialize params;
      response id initialize_result
  | "shutdown" ->
      shutdown_requested := true;
      response id `Null
  | "textDocument/documentSymbol" -> handle_document_symbol id params
  | "textDocument/definition" -> handle_definition id params
  | "textDocument/references" -> handle_references id params
  | "textDocument/documentHighlight" -> handle_document_highlight id params
  | "textDocument/completion" -> handle_completion id params
  | "textDocument/hover" -> handle_hover id params
  | "textDocument/formatting" -> handle_formatting id params
  | "textDocument/documentLink" -> handle_document_link id params
  | "textDocument/codeLens" -> handle_code_lens id params
  | "textDocument/codeAction" -> handle_code_action id params
  | "textDocument/semanticTokens/full" -> handle_semantic_tokens id params
  | "workspace/symbol" -> handle_workspace_symbol id params
  | "workspace/executeCommand" -> handle_execute_command id params
  | "sail/cName" -> handle_c_name id params
  | "sail/generatedC" -> handle_generated_c id params
  | "sail/documentation" -> handle_documentation id params
  | "sail/sourceMap" -> handle_source_map id params
  | "sail/type" -> handle_type_at_cursor id params
  | _ -> error_response id (-32601) ("Method not found: " ^ method_)

let handle_did_open params =
  match json_member "textDocument" params with
  | Some text_document -> (
      match (json_string_member "uri" text_document, json_string_member "text" text_document) with
      | Some uri, Some text ->
          clear_compiler_env_cache ();
          Hashtbl.replace text_documents uri text;
          run_diagnostics_for_uri uri
      | _ -> ()
    )
  | None -> ()

let handle_did_change params =
  match json_member "textDocument" params with
  | Some text_document -> (
      match (json_string_member "uri" text_document, json_list_member "contentChanges" params) with
      | Some uri, Some changes -> (
          match List.rev changes with
          | change :: _ -> (
              match json_string_member "text" change with
              | Some text ->
                  clear_compiler_env_cache ();
                  Hashtbl.replace text_documents uri text
              | None -> ()
            )
          | [] -> ()
        )
      | _ -> ()
    )
  | None -> ()

let handle_did_close params =
  match text_document_uri params with
  | Some uri ->
      clear_compiler_env_cache ();
      Hashtbl.remove text_documents uri;
      publish_diagnostics uri []
  | None -> ()

let handle_did_save params =
  clear_compiler_env_cache ();
  match text_document_uri params with Some uri -> run_diagnostics_for_uri uri | None -> ()

let watched_file_change_path = function
  | `Assoc _ as change -> Option.map path_of_uri (json_string_member "uri" change)
  | _ -> None

let handle_watched_files_changed params =
  match json_list_member "changes" params with
  | Some changes ->
      let paths = List.filter_map watched_file_change_path changes in
      let invalidates_cache = List.exists workspace_change_invalidates_cache paths in
      let affects_diagnostics = List.exists workspace_change_affects_diagnostics paths in
      if invalidates_cache then clear_compiler_env_cache ();
      if affects_diagnostics then run_diagnostics_for_open_documents ()
  | None -> ()

let handle_notification method_ params =
  match method_ with
  | "initialized" -> ()
  | "textDocument/didOpen" -> handle_did_open params
  | "textDocument/didChange" -> handle_did_change params
  | "textDocument/didSave" -> handle_did_save params
  | "textDocument/didClose" -> handle_did_close params
  | "workspace/didChangeWatchedFiles" -> handle_watched_files_changed params
  | "exit" -> exit (if !shutdown_requested then 0 else 1)
  | _ -> ()

let handle_message body =
  match Json.from_string body with
  | `Assoc _ as msg -> (
      match (json_member "id" msg, json_string_member "method" msg, json_member "params" msg) with
      | Some id, Some method_, Some params -> handle_request id method_ params
      | Some id, Some method_, None -> handle_request id method_ `Null
      | None, Some method_, Some params -> handle_notification method_ params
      | None, Some method_, None -> handle_notification method_ `Null
      | _ -> ()
    )
  | _ -> ()

let rec loop () =
  match read_message () with
  | None -> ()
  | Some body -> (
      try
        handle_message body;
        loop ()
      with exn ->
        Printf.eprintf "sail_lsp: %s\n%!" (Printexc.to_string exn);
        loop ()
    )

let () = loop ()
