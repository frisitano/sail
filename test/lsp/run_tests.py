#!/usr/bin/env python3

import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import threading
import time

mydir = os.path.realpath(os.path.dirname(__file__))
os.chdir(mydir)
sys.path.insert(0, os.path.realpath(".."))

from sailtest import banner, color, print_ok


repo_root = os.path.realpath(os.path.join(mydir, "..", ".."))
fixtures = os.path.join(mydir, "fixtures")


def resolve_tool(env_name, fallback, local_path):
    env_value = os.environ.get(env_name)
    if env_value:
        return env_value
    local = os.path.join(repo_root, local_path)
    if os.path.exists(local):
        return local
    found = shutil.which(fallback)
    if found:
        return found
    raise RuntimeError(f"Unable to find {fallback}. Set {env_name}.")


def file_uri(path):
    return pathlib.Path(os.path.realpath(path)).as_uri()


def position_of(text, needle, needle_offset=0):
    offset = text.index(needle) + needle_offset
    before = text[:offset]
    return {"line": before.count("\n"), "character": len(before.rsplit("\n", 1)[-1])}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


class LspClient:
    def __init__(self, argv):
        self.process = subprocess.Popen(
            argv,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=False,
        )
        self.next_id = 1
        self.notifications = []
        self.stderr_chunks = []
        self._stderr_thread = threading.Thread(target=self._drain_stderr, daemon=True)
        self._stderr_thread.start()

    def _drain_stderr(self):
        while True:
            chunk = self.process.stderr.readline()
            if not chunk:
                return
            self.stderr_chunks.append(chunk.decode("utf-8", "replace"))

    def send(self, message):
        body = json.dumps(message, separators=(",", ":")).encode("utf-8")
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
        self.process.stdin.write(header + body)
        self.process.stdin.flush()

    def notify(self, method, params=None):
        self.send({"jsonrpc": "2.0", "method": method, "params": params or {}})

    def request(self, method, params=None):
        request_id = self.next_id
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": request_id, "method": method, "params": params or {}})
        return self.read_response(request_id)

    def read_message(self, timeout=5.0):
        deadline = time.time() + timeout
        headers = {}
        while True:
            if time.time() > deadline:
                raise TimeoutError("Timed out waiting for LSP message")
            line = self.process.stdout.readline()
            if not line:
                raise RuntimeError("LSP server exited while reading headers")
            line = line.decode("ascii", "replace").rstrip("\r\n")
            if line == "":
                break
            key, value = line.split(":", 1)
            headers[key.lower()] = value.strip()
        length = int(headers["content-length"])
        body = self.process.stdout.read(length)
        return json.loads(body.decode("utf-8"))

    def read_response(self, request_id):
        while True:
            message = self.read_message()
            if message.get("id") == request_id:
                if "error" in message:
                    raise AssertionError(message["error"])
                return message.get("result")
            self.notifications.append(message)

    def wait_for_notification(self, method, predicate=lambda _params: True, timeout=5.0):
        deadline = time.time() + timeout
        while time.time() < deadline:
            for index, message in enumerate(self.notifications):
                if message.get("method") == method and predicate(message.get("params", {})):
                    return self.notifications.pop(index).get("params", {})
            message = self.read_message(timeout=max(0.1, deadline - time.time()))
            if message.get("method") == method and predicate(message.get("params", {})):
                return message.get("params", {})
            self.notifications.append(message)
        raise TimeoutError(f"Timed out waiting for {method}")

    def close(self):
        try:
            self.request("shutdown")
            self.notify("exit")
        finally:
            try:
                self.process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.process.terminate()
                self.process.wait(timeout=2)
        if self.process.returncode not in (0, None):
            stderr = "".join(self.stderr_chunks)
            raise AssertionError(f"LSP server exited with {self.process.returncode}\n{stderr}")


def text_document(uri, text):
    return {"uri": uri, "languageId": "sail", "version": 1, "text": text}


def cursor_params(uri, position):
    return {"textDocument": {"uri": uri}, "position": position}


def run_navigation_smoke(sail_lsp):
    main_path = os.path.join(fixtures, "main.sail")
    defs_path = os.path.join(fixtures, "defs.sail")
    generated_path = os.path.join(fixtures, "generated.c")
    c_map_path = os.path.join(fixtures, "generated.c.symbols.json")
    docinfo_path = os.path.join(fixtures, "docinfo.json")
    main_text = open(main_path, encoding="utf-8").read()
    defs_text = open(defs_path, encoding="utf-8").read()
    main_uri = file_uri(main_path)
    defs_uri = file_uri(defs_path)
    generated_uri = file_uri(generated_path)

    client = LspClient([sail_lsp, "--stdio"])
    try:
        init = client.request(
            "initialize",
            {
                "rootUri": file_uri(fixtures),
                "initializationOptions": {
                    "diagnostics": False,
                    "cOutput": generated_path,
                    "cMap": c_map_path,
                    "docinfo": docinfo_path,
                },
            },
        )
        caps = init["capabilities"]
        require(caps.get("definitionProvider") is True, "definition provider not advertised")
        require(caps.get("documentHighlightProvider") is True, "document highlight provider not advertised")
        require(caps.get("documentLinkProvider"), "document link provider not advertised")
        require(caps.get("codeLensProvider"), "code lens provider not advertised")
        require(caps.get("semanticTokensProvider"), "semantic tokens not advertised")
        require(caps.get("completionProvider"), "completion provider not advertised")
        trigger_chars = set(caps["completionProvider"].get("triggerCharacters", []))
        require(
            {"<", '"', "/", "."}.issubset(trigger_chars),
            "completion provider missing include path trigger characters",
        )

        client.notify("textDocument/didOpen", {"textDocument": text_document(defs_uri, defs_text)})
        client.notify("textDocument/didOpen", {"textDocument": text_document(main_uri, main_text)})

        symbols = client.request("textDocument/documentSymbol", {"textDocument": {"uri": main_uri}})
        require(any(symbol["name"] == "call_foo" for symbol in symbols), "document symbols missing call_foo")

        call_position = position_of(main_text, "= foo()", 2)
        definition = client.request("textDocument/definition", cursor_params(main_uri, call_position))
        require(definition["uri"] == defs_uri, "default definition did not resolve to Sail source")
        require(definition["range"]["start"]["line"] == 4, "default definition did not select function body")

        generated = client.request("sail/generatedC", cursor_params(main_uri, call_position))
        require(generated["uri"] == generated_uri, "generated-C request did not resolve generated file")
        require(generated["range"]["start"] == {"line": 0, "character": 5}, "generated-C request ignored sidecar cRange")

        cname = client.request("sail/cName", cursor_params(main_uri, call_position))
        require(cname["cName"] == "zfoo", "wrong generated C name")
        require(cname["source"] == "sidecar", "generated C name did not come from sidecar")

        annotation_position = position_of(main_text, "c_ext", 1)
        c_definition = client.request("textDocument/definition", cursor_params(main_uri, annotation_position))
        require(c_definition["uri"] == generated_uri, "c annotation definition did not resolve generated file")
        require(c_definition["range"]["start"]["line"] == 7, "c annotation definition used wrong C range")

        documentation = client.request("sail/documentation", cursor_params(main_uri, call_position))
        require("Fixture function" in documentation["markdown"], "documentation lookup missing fixture comment")
        require(documentation["type"] == "unit -> unit", "documentation lookup missing type metadata")
        require(documentation["url"] == "https://example.invalid/sail-docs#foo", "documentation lookup missing doc URL")

        type_info = client.request("sail/type", cursor_params(main_uri, call_position))
        require(type_info["type"] == "unit -> unit", "type-at-cursor lookup missing docinfo type")

        hover = client.request("textDocument/hover", cursor_params(main_uri, call_position))
        require("Generated C" in hover["contents"]["value"], "hover missing generated-C section")

        references = client.request(
            "textDocument/references",
            {
                "textDocument": {"uri": main_uri},
                "position": call_position,
                "context": {"includeDeclaration": True},
            },
        )
        require(len(references) >= 2, "references did not include cross-file occurrences")
        references_without_declarations = client.request(
            "textDocument/references",
            {
                "textDocument": {"uri": main_uri},
                "position": call_position,
                "context": {"includeDeclaration": False},
            },
        )
        require(
            len(references_without_declarations) < len(references),
            "references ignored includeDeclaration=false",
        )
        require(
            not any(
                reference["uri"] == defs_uri and reference["range"]["start"]["line"] in (2, 4)
                for reference in references_without_declarations
            ),
            "references without declarations still included defs.sail declarations",
        )

        declaration_position = position_of(main_text, "call_foo")
        highlights = client.request("textDocument/documentHighlight", cursor_params(main_uri, declaration_position))
        require(
            sorted(highlight["range"]["start"]["line"] for highlight in highlights) == [2, 4],
            "document highlights did not use same-file reference ranges",
        )

        workspace_symbols = client.request("workspace/symbol", {"query": "foo"})
        require(any(symbol["name"] == "foo" for symbol in workspace_symbols), "workspace symbols missing foo")

        completion_position = position_of(main_text, "= foo()", 4)
        completions = client.request("textDocument/completion", cursor_params(main_uri, completion_position))
        completion_items = completions["items"]
        foo_completion = next((item for item in completion_items if item["label"] == "foo"), None)
        require(foo_completion, "completions missing cross-file foo")
        require(foo_completion["kind"] == 3, "foo completion did not advertise function kind")
        require("unit -> unit" in foo_completion["detail"], "foo completion missing type detail")
        require(
            "Fixture function" in foo_completion["documentation"]["value"],
            "foo completion missing docinfo documentation",
        )
        keyword_position = position_of(main_text, "function call_foo", 2)
        keyword_completions = client.request("textDocument/completion", cursor_params(main_uri, keyword_position))
        function_keyword = next(
            (item for item in keyword_completions["items"] if item["label"] == "function"),
            None,
        )
        require(function_keyword, "completions missing Sail keyword")
        require(function_keyword["kind"] == 14, "Sail keyword completion used wrong kind")

        include_position = position_of(main_text, "$include <prelude.sail>", len("$include <"))
        include_completions = client.request("textDocument/completion", cursor_params(main_uri, include_position))
        include_items = include_completions["items"]
        defs_include = next((item for item in include_items if item["label"] == "defs.sail"), None)
        require(defs_include, "include completions missing workspace Sail file")
        require(defs_include["kind"] == 17, "include file completion used wrong kind")
        require(defs_include["detail"] == "Sail include file", "include file completion used wrong detail")
        require(defs_include["textEdit"]["newText"] == "defs.sail", "include file completion inserted wrong path")
        require(
            defs_include["textEdit"]["range"]["start"] == include_position,
            "include file completion replaced text before the include path",
        )

        prelude_position = position_of(main_text, "$include <prelude", len("$include <pre"))
        prelude_completions = client.request("textDocument/completion", cursor_params(main_uri, prelude_position))
        prelude_include = next(
            (item for item in prelude_completions["items"] if item["label"] == "prelude.sail"),
            None,
        )
        require(prelude_include, "include completions missing compiler library prelude")
        require(prelude_include["textEdit"]["newText"] == "prelude.sail", "include prelude completion inserted wrong path")

        parameter_position = position_of(main_text, "param_alpha\n}", len("param_al"))
        parameter_completions = client.request("textDocument/completion", cursor_params(main_uri, parameter_position))
        parameter_completion = next(
            (item for item in parameter_completions["items"] if item["label"] == "param_alpha"),
            None,
        )
        require(parameter_completion, "completions missing enclosing function parameter")
        require(parameter_completion["kind"] == 6, "parameter completion did not advertise variable kind")
        require(parameter_completion["detail"] == "parameter", "parameter completion used wrong detail")

        parameter_use_position = position_of(main_text, "param_alpha\n}", 1)
        parameter_definition = client.request("textDocument/definition", cursor_params(main_uri, parameter_use_position))
        require(parameter_definition["uri"] == main_uri, "parameter definition did not stay in source file")
        require(
            parameter_definition["range"]["start"] == position_of(main_text, "param_alpha : int"),
            "parameter definition did not resolve to function header binder",
        )

        pattern_position = position_of(
            main_text,
            "pattern_alpha + pattern_beta",
            len("pattern_alpha + pattern_be"),
        )
        pattern_completions = client.request("textDocument/completion", cursor_params(main_uri, pattern_position))
        pattern_completion = next(
            (item for item in pattern_completions["items"] if item["label"] == "pattern_beta"),
            None,
        )
        require(pattern_completion, "completions missing tuple-pattern local binder")
        require(pattern_completion["kind"] == 6, "tuple-pattern completion did not advertise variable kind")
        require(pattern_completion["detail"] == "local let", "tuple-pattern completion used wrong detail")

        pattern_use_position = position_of(
            main_text,
            "pattern_alpha + pattern_beta",
            len("pattern_alpha + p"),
        )
        pattern_definition = client.request("textDocument/definition", cursor_params(main_uri, pattern_use_position))
        require(pattern_definition["uri"] == main_uri, "tuple-pattern definition did not stay in source file")
        require(
            pattern_definition["range"]["start"] == position_of(main_text, "pattern_beta) ="),
            "tuple-pattern definition did not resolve to let-pattern binder",
        )

        struct_pattern_position = position_of(
            main_text,
            "other_probe + struct_pattern_value",
            len("other_probe + struct_pattern_val"),
        )
        struct_pattern_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, struct_pattern_position),
        )
        struct_pattern_completion = next(
            (item for item in struct_pattern_completions["items"] if item["label"] == "struct_pattern_value"),
            None,
        )
        require(struct_pattern_completion, "completions missing struct-pattern local binder")
        require(
            struct_pattern_completion["kind"] == 6,
            "struct-pattern local binder completion did not advertise variable kind",
        )
        require(
            struct_pattern_completion["detail"] == "local let",
            "struct-pattern local binder completion used wrong detail",
        )

        struct_pattern_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, struct_pattern_position),
        )
        require(
            struct_pattern_definition["uri"] == main_uri,
            "struct-pattern definition did not stay in source file",
        )
        require(
            struct_pattern_definition["range"]["start"] == position_of(main_text, "struct_pattern_value,"),
            "struct-pattern definition did not resolve to RHS binder",
        )

        record_label_probe_position = position_of(main_text, "record_probe;", len("record"))
        record_label_probe_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, record_label_probe_position),
        )
        require(
            all(item["label"] != "record_field" for item in record_label_probe_completions["items"]),
            "struct-pattern field label leaked as local binder",
        )

        other_label_probe_position = position_of(
            main_text,
            "other_probe + struct_pattern_value",
            len("other"),
        )
        other_label_probe_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, other_label_probe_position),
        )
        require(
            all(item["label"] != "other_field" for item in other_label_probe_completions["items"]),
            "struct-pattern wildcard field label leaked as local binder",
        )

        var_position = position_of(main_text, "mutable_alpha\n}", len("mutable_al"))
        var_completions = client.request("textDocument/completion", cursor_params(main_uri, var_position))
        var_completion = next((item for item in var_completions["items"] if item["label"] == "mutable_alpha"), None)
        require(var_completion, "completions missing mutable local var binder")
        require(var_completion["kind"] == 6, "mutable local var completion did not advertise variable kind")
        require(var_completion["detail"] == "local let", "mutable local var completion used wrong detail")

        var_use_position = position_of(main_text, "mutable_alpha\n}", len("mut"))
        var_definition = client.request("textDocument/definition", cursor_params(main_uri, var_use_position))
        require(var_definition["uri"] == main_uri, "mutable local var definition did not stay in source file")
        require(
            var_definition["range"]["start"] == position_of(main_text, "mutable_alpha : int"),
            "mutable local var definition did not resolve to var binder",
        )

        match_payload_position = position_of(main_text, "      match_payload\n", len("      match_pay"))
        match_payload_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, match_payload_position),
        )
        match_payload_completion = next(
            (item for item in match_payload_completions["items"] if item["label"] == "match_payload"),
            None,
        )
        require(match_payload_completion, "completions missing match-arm pattern binder")
        require(match_payload_completion["kind"] == 6, "match-arm binder completion did not advertise variable kind")
        require(
            match_payload_completion["detail"] == "pattern binder",
            "match-arm binder completion used wrong detail",
        )

        match_payload_use_position = position_of(main_text, "      match_payload\n", len("      m"))
        match_payload_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, match_payload_use_position),
        )
        require(match_payload_definition["uri"] == main_uri, "match-arm definition did not stay in source file")
        require(
            match_payload_definition["range"]["start"] == position_of(main_text, "match_payload) =>"),
            "match-arm definition did not resolve to pattern binder",
        )

        as_alias_position = position_of(main_text, "      alias_payload\n", len("      alias_pay"))
        as_alias_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, as_alias_position),
        )
        as_alias_completion = next(
            (item for item in as_alias_completions["items"] if item["label"] == "alias_payload"),
            None,
        )
        require(as_alias_completion, "completions missing as-pattern alias binder")
        require(as_alias_completion["kind"] == 6, "as-pattern alias completion did not advertise variable kind")
        require(
            as_alias_completion["detail"] == "pattern binder",
            "as-pattern alias completion used wrong detail",
        )

        as_alias_use_position = position_of(main_text, "      alias_payload\n", len("      a"))
        as_alias_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, as_alias_use_position),
        )
        require(as_alias_definition["uri"] == main_uri, "as-pattern alias definition did not stay in source file")
        require(
            as_alias_definition["range"]["start"] == position_of(main_text, "alias_payload =>"),
            "as-pattern alias definition did not resolve to pattern binder",
        )

        list_tail_position = position_of(
            main_text,
            "list_tail_payload;",
            len("list_tail_pay"),
        )
        list_tail_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, list_tail_position),
        )
        list_tail_completion = next(
            (item for item in list_tail_completions["items"] if item["label"] == "list_tail_payload"),
            None,
        )
        require(list_tail_completion, "completions missing list-cons tail pattern binder")
        require(
            list_tail_completion["detail"] == "pattern binder",
            "list-cons tail pattern binder completion used wrong detail",
        )
        list_tail_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, list_tail_position),
        )
        require(list_tail_definition["uri"] == main_uri, "list-cons tail definition did not stay in source file")
        require(
            list_tail_definition["range"]["start"] == position_of(main_text, "list_tail_payload =>"),
            "list-cons tail definition did not resolve to pattern binder",
        )

        list_head_position = position_of(
            main_text,
            "list_head_payload + list_tail_probe",
            len("list_head_pay"),
        )
        list_head_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, list_head_position),
        )
        require(
            list_head_definition["range"]["start"] == position_of(main_text, "list_head_payload ::"),
            "list-cons head definition did not resolve to pattern binder",
        )
        list_tail_references = client.request(
            "textDocument/references",
            {
                "textDocument": {"uri": main_uri},
                "position": list_tail_position,
                "context": {"includeDeclaration": True},
            },
        )
        list_tail_reference_starts = sorted(
            (
                reference["range"]["start"]["line"],
                reference["range"]["start"]["character"],
            )
            for reference in list_tail_references
        )
        list_tail_header_start = position_of(main_text, "list_tail_payload =>")
        list_tail_body_start = position_of(main_text, "list_tail_payload;", len(""))
        require(
            list_tail_reference_starts
            == sorted(
                [
                    (list_tail_header_start["line"], list_tail_header_start["character"]),
                    (list_tail_body_start["line"], list_tail_body_start["character"]),
                ]
            ),
            "list-cons tail references were not restricted to the local binder",
        )
        list_cons_after_position = position_of(
            main_text,
            "function use_inline_match_binder",
            len("function use_inline_"),
        )
        list_cons_after_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, list_cons_after_position),
        )
        require(
            all(
                item["label"] not in {"list_head_payload", "list_tail_payload"}
                for item in list_cons_after_completions["items"]
            ),
            "list-cons pattern binder leaked after match arm",
        )

        guard_payload_position = position_of(
            main_text,
            "if guard_payload > 0",
            len("if guard_pay"),
        )
        guard_payload_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, guard_payload_position),
        )
        guard_payload_completion = next(
            (item for item in guard_payload_completions["items"] if item["label"] == "guard_payload"),
            None,
        )
        require(guard_payload_completion, "completions missing guarded match-arm pattern binder")
        require(
            guard_payload_completion["kind"] == 6,
            "guarded match-arm binder completion did not advertise variable kind",
        )
        require(
            guard_payload_completion["detail"] == "pattern binder",
            "guarded match-arm binder completion used wrong detail",
        )

        guard_payload_use_position = position_of(
            main_text,
            "if guard_payload > 0",
            len("if g"),
        )
        guard_payload_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, guard_payload_use_position),
        )
        require(guard_payload_definition["uri"] == main_uri, "guarded match-arm definition did not stay in source file")
        require(
            guard_payload_definition["range"]["start"] == position_of(main_text, "guard_payload) if"),
            "guarded match-arm definition did not resolve to pattern binder",
        )

        guard_payload_body_position = position_of(
            main_text,
            "=> guard_payload",
            len("=> g"),
        )
        guard_payload_body_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, guard_payload_body_position),
        )
        require(
            guard_payload_body_definition["range"]["start"] == position_of(main_text, "guard_payload) if"),
            "same-line match-arm body definition did not resolve to pattern binder",
        )

        inline_payload_position = position_of(
            main_text,
            "if inline_payload > 0",
            len("if inline_pay"),
        )
        inline_payload_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, inline_payload_position),
        )
        inline_payload_completion = next(
            (item for item in inline_payload_completions["items"] if item["label"] == "inline_payload"),
            None,
        )
        require(inline_payload_completion, "completions missing inline match-arm pattern binder")
        require(
            inline_payload_completion["kind"] == 6,
            "inline match-arm binder completion did not advertise variable kind",
        )
        require(
            inline_payload_completion["detail"] == "pattern binder",
            "inline match-arm binder completion used wrong detail",
        )

        inline_payload_guard_use_position = position_of(
            main_text,
            "if inline_payload > 0",
            len("if i"),
        )
        inline_payload_guard_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, inline_payload_guard_use_position),
        )
        require(
            inline_payload_guard_definition["range"]["start"] == position_of(main_text, "inline_payload) if"),
            "inline match-arm guard definition did not resolve to pattern binder",
        )

        inline_payload_body_position = position_of(
            main_text,
            "=> inline_payload",
            len("=> i"),
        )
        inline_payload_body_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, inline_payload_body_position),
        )
        require(
            inline_payload_body_definition["range"]["start"] == position_of(main_text, "inline_payload) if"),
            "inline match-arm body definition did not resolve to pattern binder",
        )

        wildcard_arm_position = position_of(main_text, "_ => 0 };", len("_ => "))
        wildcard_arm_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, wildcard_arm_position),
        )
        require(
            all(item["label"] != "inline_payload" for item in wildcard_arm_completions["items"]),
            "inline match-arm binder leaked into following wildcard arm",
        )

        multiline_payload_guard_position = position_of(
            main_text,
            "        if multiline_payload > 0",
            len("        if multiline_pay"),
        )
        multiline_payload_guard_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, multiline_payload_guard_position),
        )
        multiline_payload_guard_completion = next(
            (item for item in multiline_payload_guard_completions["items"] if item["label"] == "multiline_payload"),
            None,
        )
        require(
            multiline_payload_guard_completion,
            "completions missing multi-line match-arm pattern binder in guard",
        )
        require(
            multiline_payload_guard_completion["kind"] == 6,
            "multi-line match-arm binder completion did not advertise variable kind",
        )
        require(
            multiline_payload_guard_completion["detail"] == "pattern binder",
            "multi-line match-arm binder completion used wrong detail",
        )

        multiline_payload_guard_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, multiline_payload_guard_position),
        )
        require(
            multiline_payload_guard_definition["range"]["start"]
            == position_of(main_text, "multiline_payload\n      )"),
            "multi-line match-arm guard definition did not resolve to pattern binder",
        )

        multiline_payload_body_position = position_of(
            main_text,
            "nested_payload_result : int = multiline_payload + 1",
            len("nested_payload_result : int = multi"),
        )
        multiline_payload_body_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, multiline_payload_body_position),
        )
        multiline_payload_body_completion = next(
            (item for item in multiline_payload_body_completions["items"] if item["label"] == "multiline_payload"),
            None,
        )
        require(
            multiline_payload_body_completion,
            "completions missing multi-line match-arm pattern binder in nested body",
        )
        multiline_payload_body_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, multiline_payload_body_position),
        )
        require(
            multiline_payload_body_definition["range"]["start"]
            == position_of(main_text, "multiline_payload\n      )"),
            "multi-line match-arm body definition did not resolve to pattern binder",
        )

        multiline_following_arm_position = position_of(main_text, "      UnionBeta(_) => 0", len("      UnionBeta(_) => "))
        multiline_following_arm_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, multiline_following_arm_position),
        )
        require(
            all(item["label"] != "multiline_payload" for item in multiline_following_arm_completions["items"]),
            "multi-line match-arm binder leaked into following arm",
        )

        loop_index_position = position_of(
            main_text,
            "loop_acc = loop_acc + loop_index",
            len("loop_acc = loop_acc + loop_ind"),
        )
        loop_index_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, loop_index_position),
        )
        loop_index_completion = next(
            (item for item in loop_index_completions["items"] if item["label"] == "loop_index"),
            None,
        )
        require(loop_index_completion, "completions missing foreach loop binder")
        require(loop_index_completion["kind"] == 6, "foreach loop binder completion did not advertise variable kind")
        require(loop_index_completion["detail"] == "loop binder", "foreach loop binder completion used wrong detail")

        loop_index_use_position = position_of(
            main_text,
            "loop_acc = loop_acc + loop_index",
            len("loop_acc = loop_acc + l"),
        )
        loop_index_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, loop_index_use_position),
        )
        require(loop_index_definition["uri"] == main_uri, "foreach loop definition did not stay in source file")
        require(
            loop_index_definition["range"]["start"] == position_of(main_text, "loop_index from"),
            "foreach loop definition did not resolve to loop binder",
        )

        loop_after_position = position_of(
            main_text,
            "  loop_acc\n}\n\nval use_multiline_loop_binder",
            len("  loop_"),
        )
        loop_after_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, loop_after_position),
        )
        require(
            all(item["label"] != "loop_index" for item in loop_after_completions["items"]),
            "foreach loop binder leaked after braced loop body",
        )

        multiline_loop_index_position = position_of(
            main_text,
            "multiline_loop_acc = multiline_loop_acc + multiline_loop_index",
            len("multiline_loop_acc = multiline_loop_acc + multiline_loop_ind"),
        )
        multiline_loop_index_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, multiline_loop_index_position),
        )
        multiline_loop_index_completion = next(
            (
                item
                for item in multiline_loop_index_completions["items"]
                if item["label"] == "multiline_loop_index"
            ),
            None,
        )
        require(multiline_loop_index_completion, "completions missing multi-line foreach loop binder")
        require(
            multiline_loop_index_completion["detail"] == "loop binder",
            "multi-line foreach loop binder completion used wrong detail",
        )

        multiline_loop_index_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, multiline_loop_index_position),
        )
        require(
            multiline_loop_index_definition["range"]["start"]
            == position_of(main_text, "multiline_loop_index\n    from"),
            "multi-line foreach loop definition did not resolve to loop binder",
        )

        multiline_loop_after_position = position_of(
            main_text,
            "  multiline_loop_acc\n}\n\nval use_unbraced_loop_binder",
            len("  multiline_loop_"),
        )
        multiline_loop_after_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, multiline_loop_after_position),
        )
        require(
            all(item["label"] != "multiline_loop_index" for item in multiline_loop_after_completions["items"]),
            "multi-line foreach loop binder leaked after loop body",
        )

        unbraced_loop_index_position = position_of(
            main_text,
            "unbraced_loop_acc = unbraced_loop_acc + unbraced_loop_index",
            len("unbraced_loop_acc = unbraced_loop_acc + unbraced_loop_ind"),
        )
        unbraced_loop_index_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, unbraced_loop_index_position),
        )
        unbraced_loop_index_completion = next(
            (item for item in unbraced_loop_index_completions["items"] if item["label"] == "unbraced_loop_index"),
            None,
        )
        require(unbraced_loop_index_completion, "completions missing unbraced foreach loop binder")
        require(
            unbraced_loop_index_completion["detail"] == "loop binder",
            "unbraced foreach loop binder completion used wrong detail",
        )

        unbraced_loop_index_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, unbraced_loop_index_position),
        )
        require(
            unbraced_loop_index_definition["range"]["start"] == position_of(main_text, "unbraced_loop_index from"),
            "unbraced foreach loop definition did not resolve to loop binder",
        )

        unbraced_loop_after_position = position_of(
            main_text,
            "  unbraced_loop_acc\n}\n\nunion MappingUnion",
            len("  unbraced_loop_"),
        )
        unbraced_loop_after_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, unbraced_loop_after_position),
        )
        require(
            all(item["label"] != "unbraced_loop_index" for item in unbraced_loop_after_completions["items"]),
            "unbraced foreach loop binder leaked after loop body",
        )

        mapping_payload_position = position_of(
            main_text,
            "MappingI(mapping_payload) <-> mapping_payload",
            len("MappingI(mapping_payload) <-> mapping_"),
        )
        mapping_payload_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, mapping_payload_position),
        )
        mapping_payload_completion = next(
            (item for item in mapping_payload_completions["items"] if item["label"] == "mapping_payload"),
            None,
        )
        require(mapping_payload_completion, "completions missing mapping-clause binder")
        require(
            mapping_payload_completion["kind"] == 6,
            "mapping-clause binder completion did not advertise variable kind",
        )
        require(
            mapping_payload_completion["detail"] == "mapping binder",
            "mapping-clause binder completion used wrong detail",
        )

        mapping_payload_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, mapping_payload_position),
        )
        require(mapping_payload_definition["uri"] == main_uri, "mapping-clause definition did not stay in source file")
        require(
            mapping_payload_definition["range"]["start"] == position_of(main_text, "mapping_payload) <->"),
            "mapping-clause definition did not resolve to mapping binder",
        )

        mapping_guard_position = position_of(
            main_text,
            "if mapping_guard_payload > 0",
            len("if mapping_guard_"),
        )
        mapping_guard_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, mapping_guard_position),
        )
        mapping_guard_completion = next(
            (item for item in mapping_guard_completions["items"] if item["label"] == "mapping_guard_payload"),
            None,
        )
        require(mapping_guard_completion, "completions missing mapping-clause binder in guard")
        mapping_guard_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, mapping_guard_position),
        )
        require(
            mapping_guard_definition["range"]["start"] == position_of(main_text, "mapping_guard_payload) if"),
            "mapping-clause guard definition did not resolve to mapping binder",
        )

        mapping_after_position = position_of(
            main_text,
            "function mapping_after_binder",
            len("function mapping_"),
        )
        mapping_after_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, mapping_after_position),
        )
        require(
            all(
                item["label"] not in {"mapping_payload", "mapping_guard_payload", "mapping_no_leak_payload"}
                for item in mapping_after_completions["items"]
            ),
            "mapping-clause binder leaked after mapping body",
        )

        clause_payload_position = position_of(
            main_text,
            "MappingI(clause_payload) <-> clause_payload",
            len("MappingI(clause_payload) <-> clause_"),
        )
        clause_payload_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, clause_payload_position),
        )
        clause_payload_completion = next(
            (item for item in clause_payload_completions["items"] if item["label"] == "clause_payload"),
            None,
        )
        require(clause_payload_completion, "completions missing top-level mapping clause binder")
        require(
            clause_payload_completion["detail"] == "mapping binder",
            "top-level mapping clause binder completion used wrong detail",
        )
        clause_payload_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, clause_payload_position),
        )
        require(
            clause_payload_definition["range"]["start"] == position_of(main_text, "clause_payload) <->"),
            "top-level mapping clause definition did not resolve to mapping binder",
        )

        clause_after_position = position_of(
            main_text,
            "function clause_after_mapping",
            len("function clause_"),
        )
        clause_after_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, clause_after_position),
        )
        require(
            all(item["label"] != "clause_payload" for item in clause_after_completions["items"]),
            "top-level mapping clause binder leaked after clause",
        )

        function_clause_payload_position = position_of(
            main_text,
            "  function_clause_payload\n}",
            len("  function_clause_pay"),
        )
        function_clause_payload_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, function_clause_payload_position),
        )
        function_clause_payload_completion = next(
            (
                item
                for item in function_clause_payload_completions["items"]
                if item["label"] == "function_clause_payload"
            ),
            None,
        )
        require(function_clause_payload_completion, "completions missing function-clause pattern binder")
        require(
            function_clause_payload_completion["kind"] == 6,
            "function-clause pattern binder completion did not advertise variable kind",
        )
        require(
            function_clause_payload_completion["detail"] == "pattern binder",
            "function-clause pattern binder completion used wrong detail",
        )
        function_clause_payload_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, function_clause_payload_position),
        )
        require(
            function_clause_payload_definition["range"]["start"]
            == position_of(main_text, "function_clause_payload)) -> int"),
            "function-clause pattern definition did not resolve to header binder",
        )
        function_clause_payload_references = client.request(
            "textDocument/references",
            {
                "textDocument": {"uri": main_uri},
                "position": function_clause_payload_position,
                "context": {"includeDeclaration": True},
            },
        )
        function_clause_reference_starts = sorted(
            (
                reference["range"]["start"]["line"],
                reference["range"]["start"]["character"],
            )
            for reference in function_clause_payload_references
        )
        function_clause_header_start = position_of(main_text, "function_clause_payload)) -> int")
        function_clause_body_start = position_of(main_text, "  function_clause_payload\n}", len("  "))
        require(
            function_clause_reference_starts
            == sorted(
                [
                    (function_clause_header_start["line"], function_clause_header_start["character"]),
                    (function_clause_body_start["line"], function_clause_body_start["character"]),
                ]
            ),
            "function-clause pattern references were not restricted to the local binder",
        )

        tuple_function_pattern_position = position_of(
            main_text,
            "fn_tuple_left + fn_tuple_right",
            len("fn_tuple_left + fn_tuple_rig"),
        )
        tuple_function_pattern_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, tuple_function_pattern_position),
        )
        tuple_function_pattern_completion = next(
            (item for item in tuple_function_pattern_completions["items"] if item["label"] == "fn_tuple_right"),
            None,
        )
        require(tuple_function_pattern_completion, "completions missing tuple function-clause pattern binder")
        require(
            tuple_function_pattern_completion["detail"] == "pattern binder",
            "tuple function-clause pattern binder completion used wrong detail",
        )
        tuple_function_pattern_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, tuple_function_pattern_position),
        )
        require(
            tuple_function_pattern_definition["range"]["start"]
            == position_of(main_text, "fn_tuple_right)) -> int"),
            "tuple function-clause pattern definition did not resolve to header binder",
        )

        subrange_payload_position = position_of(
            main_text,
            "unsigned(subrange_payload)",
            len("unsigned(subrange_pay"),
        )
        subrange_payload_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, subrange_payload_position),
        )
        subrange_payload_completion = next(
            (item for item in subrange_payload_completions["items"] if item["label"] == "subrange_payload"),
            None,
        )
        require(subrange_payload_completion, "completions missing vector subrange pattern binder")
        require(
            subrange_payload_completion["detail"] == "pattern binder",
            "vector subrange pattern binder completion used wrong detail",
        )
        subrange_payload_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, subrange_payload_position),
        )
        require(
            subrange_payload_definition["range"]["start"] == position_of(main_text, "subrange_payload[18..11]"),
            "vector subrange pattern definition did not resolve to header binder",
        )

        scattered_payload_position = position_of(
            main_text,
            "  scattered_payload\n}",
            len("  scattered_pay"),
        )
        scattered_payload_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, scattered_payload_position),
        )
        scattered_payload_completion = next(
            (item for item in scattered_payload_completions["items"] if item["label"] == "scattered_payload"),
            None,
        )
        require(scattered_payload_completion, "completions missing scattered function-clause pattern binder")
        require(
            scattered_payload_completion["detail"] == "pattern binder",
            "scattered function-clause pattern binder completion used wrong detail",
        )
        scattered_payload_definition = client.request(
            "textDocument/definition",
            cursor_params(main_uri, scattered_payload_position),
        )
        require(
            scattered_payload_definition["range"]["start"] == position_of(main_text, "scattered_payload)) = {"),
            "scattered function-clause pattern definition did not resolve to header binder",
        )

        function_clause_after_pattern_position = position_of(
            main_text,
            "function function_clause_after_pattern",
            len("function function_clause_"),
        )
        function_clause_after_pattern_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, function_clause_after_pattern_position),
        )
        require(
            all(
                item["label"]
                not in {
                    "function_clause_payload",
                    "fn_tuple_left",
                    "fn_tuple_right",
                    "subrange_payload",
                    "scattered_payload",
                }
                for item in function_clause_after_pattern_completions["items"]
            ),
            "function-clause pattern binder leaked after clause body",
        )

        enum_position = position_of(main_text, "ChoiceAlpha", len("Choice"))
        enum_completions = client.request("textDocument/completion", cursor_params(main_uri, enum_position))
        enum_completion = next(
            (item for item in enum_completions["items"] if item["label"] == "ChoiceAlpha"),
            None,
        )
        require(enum_completion, "completions missing enum member")
        require(enum_completion["kind"] == 20, "enum member completion used wrong kind")
        require(enum_completion["detail"] == "enum member of LocalChoice", "enum member completion used wrong detail")

        expected_enum_position = position_of(
            main_text,
            "use_expected_choice() -> LocalChoice = ChoiceAlpha",
            len("use_expected_choice() -> LocalChoice = Choice"),
        )
        expected_enum_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, expected_enum_position),
        )
        expected_enum_completion = next(
            (item for item in expected_enum_completions["items"] if item["label"] == "ChoiceAlpha"),
            None,
        )
        other_enum_completion = next(
            (item for item in expected_enum_completions["items"] if item["label"] == "ChoiceOther"),
            None,
        )
        require(expected_enum_completion, "expected-type completions missing matching enum member")
        require(other_enum_completion, "expected-type completions missing competing enum member")
        require(
            expected_enum_completion["sortText"].startswith("00_"),
            "matching enum member was not promoted by expected type",
        )
        require(
            other_enum_completion["sortText"].startswith("01_"),
            "nonmatching enum member was promoted by expected type",
        )

        local_expected_enum_position = position_of(
            main_text,
            "selected_choice : LocalChoice = ChoiceAlpha",
            len("selected_choice : LocalChoice = Choice"),
        )
        local_expected_enum_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, local_expected_enum_position),
        )
        local_expected_enum_completion = next(
            (item for item in local_expected_enum_completions["items"] if item["label"] == "ChoiceAlpha"),
            None,
        )
        local_other_enum_completion = next(
            (item for item in local_expected_enum_completions["items"] if item["label"] == "ChoiceOther"),
            None,
        )
        require(local_expected_enum_completion, "local expected-type completions missing matching enum member")
        require(local_other_enum_completion, "local expected-type completions missing competing enum member")
        require(
            local_expected_enum_completion["sortText"].startswith("00_"),
            "matching local enum member was not promoted by expected type",
        )
        require(
            local_other_enum_completion["sortText"].startswith("01_"),
            "nonmatching local enum member was promoted by expected type",
        )

        constructor_position = position_of(main_text, "UnionAlpha(1)", len("Union"))
        constructor_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, constructor_position),
        )
        constructor_completion = next(
            (item for item in constructor_completions["items"] if item["label"] == "UnionAlpha"),
            None,
        )
        require(constructor_completion, "completions missing union constructor")
        require(constructor_completion["kind"] == 4, "union constructor completion used wrong kind")
        require(
            constructor_completion["detail"] == "union constructor of LocalUnion",
            "union constructor completion used wrong detail",
        )

        expected_constructor_position = position_of(
            main_text,
            "LocalUnion = UnionAlpha(1)",
            len("LocalUnion = Union"),
        )
        expected_constructor_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, expected_constructor_position),
        )
        expected_constructor_completion = next(
            (item for item in expected_constructor_completions["items"] if item["label"] == "UnionAlpha"),
            None,
        )
        other_constructor_completion = next(
            (item for item in expected_constructor_completions["items"] if item["label"] == "UnionOther"),
            None,
        )
        require(expected_constructor_completion, "expected-type completions missing matching union constructor")
        require(other_constructor_completion, "expected-type completions missing competing union constructor")
        require(
            expected_constructor_completion["sortText"].startswith("00_"),
            "matching union constructor was not promoted by expected type",
        )
        require(
            other_constructor_completion["sortText"].startswith("01_"),
            "nonmatching union constructor was promoted by expected type",
        )

        field_position = position_of(main_text, "r.record_field", len("r.record"))
        field_completions = client.request("textDocument/completion", cursor_params(main_uri, field_position))
        field_completion = next(
            (item for item in field_completions["items"] if item["label"] == "record_field"),
            None,
        )
        require(field_completion, "field-context completions missing struct field")
        require(field_completion["kind"] == 5, "struct field completion used wrong kind")
        require(
            field_completion["detail"] == "field of LocalRecord : int",
            "struct field completion used wrong detail",
        )
        other_field_completion = next(
            (item for item in field_completions["items"] if item["label"] == "record_other"),
            None,
        )
        require(other_field_completion, "field-context completions missing competing struct field")
        require(
            field_completion["sortText"].startswith("00_"),
            "receiver-owned field was not promoted",
        )
        require(
            other_field_completion["sortText"].startswith("01_"),
            "nonmatching receiver field was promoted",
        )

        local_field_position = position_of(main_text, "local_record.record_field", len("local_record.record"))
        local_field_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, local_field_position),
        )
        local_field_completion = next(
            (item for item in local_field_completions["items"] if item["label"] == "record_field"),
            None,
        )
        local_other_field_completion = next(
            (item for item in local_field_completions["items"] if item["label"] == "record_other"),
            None,
        )
        require(local_field_completion, "local receiver field completions missing struct field")
        require(local_other_field_completion, "local receiver field completions missing competing struct field")
        require(
            local_field_completion["sortText"].startswith("00_"),
            "local receiver-owned field was not promoted",
        )
        require(
            local_other_field_completion["sortText"].startswith("01_"),
            "local nonmatching receiver field was promoted",
        )

        nested_field_position = position_of(
            main_text,
            "w.inner_record.record_field",
            len("w.inner_record.record"),
        )
        nested_field_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, nested_field_position),
        )
        nested_field_completion = next(
            (item for item in nested_field_completions["items"] if item["label"] == "record_field"),
            None,
        )
        nested_other_field_completion = next(
            (item for item in nested_field_completions["items"] if item["label"] == "record_other"),
            None,
        )
        require(nested_field_completion, "nested receiver field completions missing struct field")
        require(nested_other_field_completion, "nested receiver field completions missing competing struct field")
        require(
            nested_field_completion["sortText"].startswith("00_"),
            "nested receiver-owned field was not promoted",
        )
        require(
            nested_other_field_completion["sortText"].startswith("01_"),
            "nested nonmatching receiver field was promoted",
        )

        local_nested_field_position = position_of(
            main_text,
            "local_wrapper.inner_record.record_field",
            len("local_wrapper.inner_record.record"),
        )
        local_nested_field_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, local_nested_field_position),
        )
        local_nested_field_completion = next(
            (item for item in local_nested_field_completions["items"] if item["label"] == "record_field"),
            None,
        )
        local_nested_other_field_completion = next(
            (item for item in local_nested_field_completions["items"] if item["label"] == "record_other"),
            None,
        )
        require(local_nested_field_completion, "local nested receiver field completions missing struct field")
        require(
            local_nested_other_field_completion,
            "local nested receiver field completions missing competing struct field",
        )
        require(
            local_nested_field_completion["sortText"].startswith("00_"),
            "local nested receiver-owned field was not promoted",
        )
        require(
            local_nested_other_field_completion["sortText"].startswith("01_"),
            "local nested nonmatching receiver field was promoted",
        )

        call_receiver_field_position = position_of(
            main_text,
            "make_local_record().record_field",
            len("make_local_record().record"),
        )
        call_receiver_field_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, call_receiver_field_position),
        )
        call_receiver_field_completion = next(
            (item for item in call_receiver_field_completions["items"] if item["label"] == "record_field"),
            None,
        )
        call_receiver_other_field_completion = next(
            (item for item in call_receiver_field_completions["items"] if item["label"] == "record_other"),
            None,
        )
        require(call_receiver_field_completion, "call receiver field completions missing struct field")
        require(call_receiver_other_field_completion, "call receiver field completions missing competing struct field")
        require(
            call_receiver_field_completion["sortText"].startswith("00_"),
            "call receiver-owned field was not promoted",
        )
        require(
            call_receiver_other_field_completion["sortText"].startswith("01_"),
            "call receiver nonmatching field was promoted",
        )

        call_nested_field_position = position_of(
            main_text,
            "make_wrapper_record().inner_record.record_field",
            len("make_wrapper_record().inner_record.record"),
        )
        call_nested_field_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, call_nested_field_position),
        )
        call_nested_field_completion = next(
            (item for item in call_nested_field_completions["items"] if item["label"] == "record_field"),
            None,
        )
        call_nested_other_field_completion = next(
            (item for item in call_nested_field_completions["items"] if item["label"] == "record_other"),
            None,
        )
        require(call_nested_field_completion, "call nested receiver field completions missing struct field")
        require(
            call_nested_other_field_completion,
            "call nested receiver field completions missing competing struct field",
        )
        require(
            call_nested_field_completion["sortText"].startswith("00_"),
            "call nested receiver-owned field was not promoted",
        )
        require(
            call_nested_other_field_completion["sortText"].startswith("01_"),
            "call nested receiver nonmatching field was promoted",
        )

        indexed_local_field_position = position_of(
            main_text,
            "local_records[0].record_field",
            len("local_records[0].record"),
        )
        indexed_local_field_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, indexed_local_field_position),
        )
        indexed_local_field_completion = next(
            (item for item in indexed_local_field_completions["items"] if item["label"] == "record_field"),
            None,
        )
        indexed_local_other_field_completion = next(
            (item for item in indexed_local_field_completions["items"] if item["label"] == "record_other"),
            None,
        )
        require(indexed_local_field_completion, "indexed local receiver field completions missing struct field")
        require(
            indexed_local_other_field_completion,
            "indexed local receiver field completions missing competing struct field",
        )
        require(
            indexed_local_field_completion["sortText"].startswith("00_"),
            "indexed local receiver-owned field was not promoted",
        )
        require(
            indexed_local_other_field_completion["sortText"].startswith("01_"),
            "indexed local receiver nonmatching field was promoted",
        )

        indexed_nested_field_position = position_of(
            main_text,
            "w.indexed_records[0].record_field",
            len("w.indexed_records[0].record"),
        )
        indexed_nested_field_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, indexed_nested_field_position),
        )
        indexed_nested_field_completion = next(
            (item for item in indexed_nested_field_completions["items"] if item["label"] == "record_field"),
            None,
        )
        indexed_nested_other_field_completion = next(
            (item for item in indexed_nested_field_completions["items"] if item["label"] == "record_other"),
            None,
        )
        require(indexed_nested_field_completion, "indexed nested receiver field completions missing struct field")
        require(
            indexed_nested_other_field_completion,
            "indexed nested receiver field completions missing competing struct field",
        )
        require(
            indexed_nested_field_completion["sortText"].startswith("00_"),
            "indexed nested receiver-owned field was not promoted",
        )
        require(
            indexed_nested_other_field_completion["sortText"].startswith("01_"),
            "indexed nested receiver nonmatching field was promoted",
        )

        indexed_call_field_position = position_of(
            main_text,
            "make_local_records()[0].record_field",
            len("make_local_records()[0].record"),
        )
        indexed_call_field_completions = client.request(
            "textDocument/completion",
            cursor_params(main_uri, indexed_call_field_position),
        )
        indexed_call_field_completion = next(
            (item for item in indexed_call_field_completions["items"] if item["label"] == "record_field"),
            None,
        )
        indexed_call_other_field_completion = next(
            (item for item in indexed_call_field_completions["items"] if item["label"] == "record_other"),
            None,
        )
        require(indexed_call_field_completion, "indexed call receiver field completions missing struct field")
        require(
            indexed_call_other_field_completion,
            "indexed call receiver field completions missing competing struct field",
        )
        require(
            indexed_call_field_completion["sortText"].startswith("00_"),
            "indexed call receiver-owned field was not promoted",
        )
        require(
            indexed_call_other_field_completion["sortText"].startswith("01_"),
            "indexed call receiver nonmatching field was promoted",
        )

        def require_promoted_receiver_field(source, prefix_len, label):
            field_position = position_of(main_text, source, prefix_len)
            completions = client.request("textDocument/completion", cursor_params(main_uri, field_position))
            field_completion = next(
                (item for item in completions["items"] if item["label"] == "record_field"),
                None,
            )
            other_field_completion = next(
                (item for item in completions["items"] if item["label"] == "record_other"),
                None,
            )
            require(field_completion, f"{label} completions missing struct field")
            require(other_field_completion, f"{label} completions missing competing struct field")
            require(
                field_completion["sortText"].startswith("00_"),
                f"{label} receiver-owned field was not promoted",
            )
            require(
                other_field_completion["sortText"].startswith("01_"),
                f"{label} nonmatching receiver field was promoted",
            )

        parenthesized_field_cases = [
            ("(r).record_field", len("(r).record"), "parenthesized parameter receiver"),
            (
                "(w.inner_record).record_field",
                len("(w.inner_record).record"),
                "parenthesized nested receiver",
            ),
            (
                "(make_local_record()).record_field",
                len("(make_local_record()).record"),
                "parenthesized call receiver",
            ),
            (
                "(local_records[0]).record_field",
                len("(local_records[0]).record"),
                "parenthesized indexed receiver",
            ),
            (
                "(local_records)[0].record_field",
                len("(local_records)[0].record"),
                "parenthesized outer-index receiver",
            ),
        ]
        for source, prefix_len, label in parenthesized_field_cases:
            require_promoted_receiver_field(source, prefix_len, label)

        conditional_field_cases = [
            (
                "(if flag then left else right).record_field",
                len("(if flag then left else right).record"),
                "conditional parameter receiver",
            ),
            (
                "(if flag then w.inner_record else right).record_field",
                len("(if flag then w.inner_record else right).record"),
                "conditional nested receiver",
            ),
            (
                "(if flag then make_local_record() else right).record_field",
                len("(if flag then make_local_record() else right).record"),
                "conditional call receiver",
            ),
            (
                "(if flag then local_records[0] else right).record_field",
                len("(if flag then local_records[0] else right).record"),
                "conditional indexed receiver",
            ),
        ]
        for source, prefix_len, label in conditional_field_cases:
            require_promoted_receiver_field(source, prefix_len, label)

        source_map = client.request("sail/sourceMap", {"textDocument": {"uri": main_uri}})
        call_foo_entry = next((entry for entry in source_map if entry["name"] == "call_foo"), None)
        require(call_foo_entry, "source map missing call_foo")
        require(call_foo_entry["cName"] == "zcall_foo", "source map missing generated C sidecar name")
        require(call_foo_entry["cSource"] == "sidecar", "source map missing generated C sidecar source")
        require(call_foo_entry["cLocation"]["uri"] == generated_uri, "source map missing generated C location URI")
        require(
            call_foo_entry["cLocation"]["range"]["start"] == {"line": 3, "character": 5},
            "source map missing generated C sidecar range",
        )
        require(call_foo_entry["referenceCount"] == 2, "source map missing graph reference count")
        require(
            sorted(reference["range"]["start"]["line"] for reference in call_foo_entry["references"]) == [2, 4],
            "source map missing graph reference ranges",
        )
        require(
            call_foo_entry["docUrl"] == "https://example.invalid/sail-docs#call_foo",
            "source map missing docinfo URL",
        )
        require(call_foo_entry["type"] == "unit -> unit", "source map missing type metadata")
        require(call_foo_entry["typeSource"] in ("compiler", "source"), "source map used unexpected type source")

        semantic_tokens = client.request("textDocument/semanticTokens/full", {"textDocument": {"uri": main_uri}})
        require(len(semantic_tokens.get("data", [])) > 0, "semantic tokens empty")

        code_actions = client.request(
            "textDocument/codeAction",
            {
                "textDocument": {"uri": main_uri},
                "range": {"start": call_position, "end": call_position},
                "context": {"diagnostics": []},
            },
        )
        action_titles = {action["title"] for action in code_actions}
        require("Sail: Go to Generated C" in action_titles, "code actions missing generated-C action")
        require("Sail: Show Type" in action_titles, "code actions missing type action")
        require("Sail: Show Documentation" in action_titles, "code actions missing documentation action")

        declaration_actions = client.request(
            "textDocument/codeAction",
            {
                "textDocument": {"uri": main_uri},
                "range": {"start": declaration_position, "end": declaration_position},
                "context": {"diagnostics": []},
            },
        )
        insert_annotation = next(
            (action for action in declaration_actions if action["title"] == "Sail: Insert C Annotation"),
            None,
        )
        require(insert_annotation, "code actions missing edit-producing C annotation action")
        edits = insert_annotation["edit"]["changes"][main_uri]
        require(edits[0]["newText"] == '$[c: "zcall_foo"]\n', "C annotation action inserted the wrong text")

        links = client.request("textDocument/documentLink", {"textDocument": {"uri": main_uri}})
        require(any(link.get("target") == generated_uri for link in links), "document links missing generated C target")
        require(
            any(link.get("target") == "https://example.invalid/sail-docs#call_foo" for link in links),
            "document links missing generated documentation target",
        )

        lenses = client.request("textDocument/codeLens", {"textDocument": {"uri": main_uri}})
        lens_titles = {lens["command"]["title"] for lens in lenses}
        require("Go to Generated C" in lens_titles, "code lenses missing generated-C lens")
        require("Show Type" in lens_titles, "code lenses missing type lens")
        require("Show Documentation" in lens_titles, "code lenses missing documentation lens")

        print_ok("navigation-smoke")
    finally:
        client.close()


def run_source_documentation_smoke(sail_lsp):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-source-docs-") as tempdir:
        source_path = os.path.join(tempdir, "docs.sail")
        source_text = """$include <prelude.sail>

/// Fallback source documentation.
/// Exposed when docinfo JSON is not available.
val documented : unit -> unit

function documented() = ()

function caller() = documented()
"""
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)

        source_uri = file_uri(source_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})

            call_position = position_of(source_text, "= documented()", 3)
            documentation = client.request("sail/documentation", cursor_params(source_uri, call_position))
            require(
                "Fallback source documentation" in documentation["markdown"],
                "source comment documentation fallback missing comment",
            )
            require(
                "Exposed when docinfo JSON is not available" in documentation["markdown"],
                "source comment documentation fallback missing multiline comment",
            )
            require(documentation["type"] == "unit -> unit", "source comment documentation fallback missing val type")

            hover = client.request("textDocument/hover", cursor_params(source_uri, call_position))
            require(
                "Fallback source documentation" in hover["contents"]["value"],
                "hover missing source documentation fallback",
            )

            code_actions = client.request(
                "textDocument/codeAction",
                {
                    "textDocument": {"uri": source_uri},
                    "range": {"start": call_position, "end": call_position},
                    "context": {"diagnostics": []},
                },
            )
            action_titles = {action["title"] for action in code_actions}
            require("Sail: Show Documentation" in action_titles, "code actions missing source documentation action")

            lenses = client.request("textDocument/codeLens", {"textDocument": {"uri": source_uri}})
            lens_titles = {lens["command"]["title"] for lens in lenses}
            require("Show Documentation" in lens_titles, "code lenses missing source documentation lens")

            print_ok("source-documentation-smoke")
        finally:
            client.close()


def run_c_artifact_discovery_smoke(sail_lsp):
    main_path = os.path.join(fixtures, "main.sail")
    generated_path = os.path.join(fixtures, "generated.c")
    main_text = open(main_path, encoding="utf-8").read()
    main_uri = file_uri(main_path)
    generated_uri = file_uri(generated_path)

    client = LspClient([sail_lsp, "--stdio"])
    try:
        client.request(
            "initialize",
            {
                "rootUri": file_uri(fixtures),
                "initializationOptions": {
                    "diagnostics": False,
                },
            },
        )
        client.notify("textDocument/didOpen", {"textDocument": text_document(main_uri, main_text)})

        call_position = position_of(main_text, "= foo()", 2)
        generated = client.request("sail/generatedC", cursor_params(main_uri, call_position))
        require(generated["uri"] == generated_uri, "discovered generated-C request did not resolve generated file")
        require(generated["range"]["start"] == {"line": 0, "character": 5}, "discovered generated-C request ignored cRange")

        cname = client.request("sail/cName", cursor_params(main_uri, call_position))
        require(cname["source"] == "sidecar", "discovered generated C name did not come from sidecar")

        type_info = client.request("sail/type", cursor_params(main_uri, call_position))
        require(type_info["type"] == "unit -> unit", "source-backed type lookup did not find val spec")
        require(type_info["source"] == "source", "source-backed type lookup reported wrong source")

        annotation_position = position_of(main_text, "c_ext", 1)
        c_definition = client.request("textDocument/definition", cursor_params(main_uri, annotation_position))
        require(c_definition["uri"] == generated_uri, "discovered c annotation definition did not resolve generated file")
        require(c_definition["range"]["start"]["line"] == 7, "discovered c annotation definition used wrong C range")

        print_ok("c-artifact-discovery-smoke")
    finally:
        client.close()

    with tempfile.TemporaryDirectory(prefix="sail-lsp-c-discovery-") as tempdir:
        source_path = os.path.join(tempdir, "model.sail")
        output_dir = os.path.join(tempdir, "build")
        os.mkdir(output_dir)
        generated_path = os.path.join(output_dir, "generated.c")
        with open(source_path, "w", encoding="utf-8") as output:
            output.write("$include <prelude.sail>\n\nval foo : unit -> unit\n\nfunction foo() = ()\n")
        with open(generated_path, "w", encoding="utf-8") as output:
            output.write("void zfoo(void) {}\n")

        source_text = open(source_path, encoding="utf-8").read()
        source_uri = file_uri(source_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})
            foo_position = position_of(source_text, "foo", 1)
            generated = client.request("sail/generatedC", cursor_params(source_uri, foo_position))
            require(generated["uri"] == file_uri(generated_path), "recursive C fallback did not discover generated C")
            require(generated["range"]["start"] == {"line": 0, "character": 5}, "recursive C fallback used wrong range")
        finally:
            client.close()


def run_artifact_index_smoke(sail_lsp, sail):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-artifacts-") as tempdir:
        source_dir = os.path.join(tempdir, "src")
        build_dir = os.path.join(tempdir, "build")
        os.mkdir(source_dir)
        os.mkdir(build_dir)

        source_path = os.path.join(source_dir, "model.sail")
        generated_path = os.path.join(build_dir, "model.c")
        sidecar_path = os.path.join(build_dir, "model.c.symbols.json")
        docinfo_path = os.path.join(build_dir, "doc.json")
        selected_project_path = os.path.join(tempdir, "selected.sail_project")
        ignored_project_path = os.path.join(tempdir, "ignored.sail_project")
        manifest_path = os.path.join(tempdir, "sail.lsp.json")

        source_text = "$include <prelude.sail>\n\nval foo : unit -> unit\n\nfunction foo() = ()\n"
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)
        with open(generated_path, "w", encoding="utf-8") as output:
            output.write("void zfoo(void) {}\n")
        with open(sidecar_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.c.symbols",
                    "version": 2,
                    "cFile": "model.c",
                    "symbols": [
                        {
                            "sailName": "foo",
                            "cName": "zfoo",
                            "cRange": {
                                "start": {"line": 0, "character": 5},
                                "end": {"line": 0, "character": 9},
                            },
                            "kind": "function",
                            "generated": True,
                        }
                    ],
                },
                output,
            )
        with open(docinfo_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "functions": {
                        "foo": {
                            "comment": "Manifest-discovered documentation.",
                            "type": "unit -> unit",
                            "docUrl": "https://example.invalid/sail-docs#manifest-foo",
                            "source": "function foo() = ()",
                            "location": {"file": "src/model.sail", "loc": [5, 0, 0, 5, 0, 19]},
                        }
                    }
                },
                output,
            )
        for project_path in (selected_project_path, ignored_project_path):
            with open(project_path, "w", encoding="utf-8") as output:
                output.write("{}\n")
        with open(manifest_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.lsp.artifacts",
                    "version": 1,
                    "projectFile": "selected.sail_project",
                    "projectModules": [],
                    "artifacts": {
                        "cOutput": "build/model.c",
                        "cMap": "build/model.c.symbols.json",
                        "docinfo": "build/doc.json",
                    },
                },
                output,
            )

        source_uri = file_uri(source_path)
        generated_uri = file_uri(generated_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "sail": sail,
                        "diagnostics": True,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})

            foo_position = position_of(source_text, "foo", 1)
            generated = client.request("sail/generatedC", cursor_params(source_uri, foo_position))
            require(generated["uri"] == generated_uri, "artifact index did not resolve generated C")
            require(
                generated["range"]["start"] == {"line": 0, "character": 5},
                "artifact index ignored sidecar C range",
            )

            documentation = client.request("sail/documentation", cursor_params(source_uri, foo_position))
            require(
                "Manifest-discovered documentation" in documentation["markdown"],
                "artifact index did not resolve docinfo",
            )
            require(
                documentation["url"] == "https://example.invalid/sail-docs#manifest-foo",
                "artifact index docinfo lost generated documentation URL",
            )

            diagnostics = client.wait_for_notification(
                "textDocument/publishDiagnostics",
                lambda params: params.get("uri") == source_uri,
                timeout=15.0,
            )
            require(
                not any(
                    diagnostic.get("code") == "sail.project.ambiguous"
                    for diagnostic in diagnostics.get("diagnostics", [])
                ),
                "artifact index projectFile did not suppress ambiguous project discovery",
            )

            print_ok("artifact-index-smoke")
        finally:
            client.close()


def run_watched_sidecar_refresh_smoke(sail_lsp):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-watch-sidecar-") as tempdir:
        build_dir = os.path.join(tempdir, "build")
        os.mkdir(build_dir)

        source_path = os.path.join(tempdir, "model.sail")
        generated_path = os.path.join(build_dir, "model.c")
        sidecar_path = os.path.join(build_dir, "model.c.symbols.json")
        manifest_path = os.path.join(tempdir, "sail.lsp.json")

        source_text = "$include <prelude.sail>\n\nval foo : unit -> unit\n\nfunction foo() = ()\n"
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)
        with open(generated_path, "w", encoding="utf-8") as output:
            output.write("void zfoo_old(void) {}\nvoid zfoo_new(void) {}\n")
        with open(manifest_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.lsp.artifacts",
                    "version": 1,
                    "artifacts": {
                        "cOutput": "build/model.c",
                        "cMap": "build/model.c.symbols.json",
                    },
                },
                output,
            )

        def write_sidecar(c_name, line):
            with open(sidecar_path, "w", encoding="utf-8") as output:
                json.dump(
                    {
                        "schema": "sail.c.symbols",
                        "version": 2,
                        "cFile": "model.c",
                        "symbols": [
                            {
                                "sailName": "foo",
                                "cName": c_name,
                                "cRange": {
                                    "start": {"line": line, "character": 5},
                                    "end": {"line": line, "character": 13},
                                },
                                "kind": "function",
                                "generated": True,
                            }
                        ],
                    },
                    output,
                )

        write_sidecar("zfoo_old", 0)

        source_uri = file_uri(source_path)
        generated_uri = file_uri(generated_path)
        sidecar_uri = file_uri(sidecar_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})

            def source_map_foo_entry():
                source_map = client.request("sail/sourceMap", {"textDocument": {"uri": source_uri}})
                entry = next((entry for entry in source_map if entry["name"] == "foo"), None)
                require(entry, "watched sidecar source map missing foo")
                return entry

            initial = source_map_foo_entry()
            require(initial["cName"] == "zfoo_old", "source map did not load initial sidecar C name")
            require(initial["cLocation"]["uri"] == generated_uri, "source map did not use manifest-paired C file")
            require(
                initial["cLocation"]["range"]["start"] == {"line": 0, "character": 5},
                "source map did not use initial sidecar range",
            )

            write_sidecar("zfoo_new", 1)
            client.notify(
                "workspace/didChangeWatchedFiles",
                {"changes": [{"uri": sidecar_uri, "type": 2}]},
            )

            refreshed = source_map_foo_entry()
            require(refreshed["cName"] == "zfoo_new", "watched sidecar change did not refresh source map C name")
            require(
                refreshed["cLocation"]["range"]["start"] == {"line": 1, "character": 5},
                "watched sidecar change did not refresh source map C range",
            )

            print_ok("watched-sidecar-refresh-smoke")
        finally:
            client.close()


def run_watched_diagnostics_refresh_smoke(sail_lsp, sail):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-watch-diagnostics-") as tempdir:
        source_path = os.path.join(tempdir, "model.sail")
        valid_text = "$include <prelude.sail>\n\nval foo : unit -> unit\n\nfunction foo() = ()\n"
        invalid_text = open(os.path.join(repo_root, "test", "typecheck", "fail", "infer_if_error.sail"), encoding="utf-8").read()
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(valid_text)

        source_uri = file_uri(source_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "sail": sail,
                        "diagnostics": True,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, valid_text)})
            client.wait_for_notification(
                "textDocument/publishDiagnostics",
                lambda params: params.get("uri") == source_uri,
                timeout=15.0,
            )

            with open(source_path, "w", encoding="utf-8") as output:
                output.write(invalid_text)
            client.notify(
                "workspace/didChangeWatchedFiles",
                {"changes": [{"uri": source_uri, "type": 2}]},
            )

            def has_refreshed_diagnostic(params):
                if params.get("uri") != source_uri:
                    return False
                return any(
                    diagnostic.get("code") == "sail.type.infer"
                    or "Could not infer type" in diagnostic.get("message", "")
                    for diagnostic in params.get("diagnostics", [])
                )

            client.wait_for_notification(
                "textDocument/publishDiagnostics",
                has_refreshed_diagnostic,
                timeout=15.0,
            )
            print_ok("watched-diagnostics-refresh-smoke")
        finally:
            client.close()


def run_recursive_artifact_index_smoke(sail_lsp):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-recursive-artifacts-") as tempdir:
        source_path = os.path.join(tempdir, "model.sail")
        build_dir = os.path.join(tempdir, "build")
        os.mkdir(build_dir)

        generated_path = os.path.join(build_dir, "out.c")
        sidecar_path = os.path.join(build_dir, "out.c.symbols.json")
        manifest_path = os.path.join(build_dir, "out.sail_lsp.json")

        source_text = "$include <prelude.sail>\n\nval foo : unit -> unit\n\nfunction foo() = ()\n"
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)
        with open(generated_path, "w", encoding="utf-8") as output:
            output.write("void zfoo(void) {}\n")
        with open(sidecar_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.c.symbols",
                    "version": 2,
                    "cFile": "out.c",
                    "symbols": [
                        {
                            "sailName": "foo",
                            "cName": "zfoo",
                            "cRange": {
                                "start": {"line": 0, "character": 5},
                                "end": {"line": 0, "character": 9},
                            },
                            "kind": "function",
                            "generated": True,
                        }
                    ],
                },
                output,
            )
        with open(manifest_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.lsp.artifacts",
                    "version": 1,
                    "artifacts": {
                        "cOutput": "out.c",
                        "cMap": "out.c.symbols.json",
                    },
                },
                output,
            )

        source_uri = file_uri(source_path)
        generated_uri = file_uri(generated_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})

            foo_position = position_of(source_text, "foo", 1)
            generated = client.request("sail/generatedC", cursor_params(source_uri, foo_position))
            require(generated["uri"] == generated_uri, "recursive artifact index did not resolve generated C")
            require(
                generated["range"]["start"] == {"line": 0, "character": 5},
                "recursive artifact index ignored sidecar C range",
            )

            cname = client.request("sail/cName", cursor_params(source_uri, foo_position))
            require(cname["cName"] == "zfoo", "recursive artifact index resolved wrong C name")
            require(cname["source"] == "sidecar", "recursive artifact index did not use sidecar mapping")

            print_ok("recursive-artifact-index-smoke")
        finally:
            client.close()


def run_multi_manifest_c_pairing_smoke(sail_lsp):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-manifest-pairing-") as tempdir:
        build_a = os.path.join(tempdir, "build-a")
        build_b = os.path.join(tempdir, "build-b")
        os.mkdir(build_a)
        os.mkdir(build_b)

        source_path = os.path.join(tempdir, "model.sail")
        decoy_generated_path = os.path.join(build_a, "out.c")
        decoy_sidecar_path = os.path.join(build_a, "out.c.symbols.json")
        target_generated_path = os.path.join(build_b, "out.c")
        target_sidecar_path = os.path.join(build_b, "out.c.symbols.json")
        root_manifest_path = os.path.join(tempdir, "sail.lsp.json")
        nested_manifest_path = os.path.join(build_b, "out.sail_lsp.json")

        source_text = "$include <prelude.sail>\n\nval foo : unit -> unit\n\nfunction foo() = ()\n"
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)
        with open(decoy_generated_path, "w", encoding="utf-8") as output:
            output.write("void zfoo(void) {}\n")
        with open(target_generated_path, "w", encoding="utf-8") as output:
            output.write("// target output\nvoid zfoo(void) {}\n")
        with open(decoy_sidecar_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.c.symbols",
                    "version": 2,
                    "symbols": [
                        {
                            "sailName": "decoy",
                            "cName": "zdecoy",
                            "kind": "function",
                            "generated": True,
                        }
                    ],
                },
                output,
            )
        with open(target_sidecar_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.c.symbols",
                    "version": 2,
                    "symbols": [
                        {
                            "sailName": "foo",
                            "cName": "zfoo",
                            "kind": "function",
                            "generated": True,
                        }
                    ],
                },
                output,
            )
        with open(root_manifest_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.lsp.artifacts",
                    "version": 1,
                    "artifacts": {
                        "cOutput": "build-a/out.c",
                        "cMap": "build-a/out.c.symbols.json",
                    },
                },
                output,
            )
        with open(nested_manifest_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.lsp.artifacts",
                    "version": 1,
                    "artifacts": {
                        "cOutput": "out.c",
                        "cMap": "out.c.symbols.json",
                    },
                },
                output,
            )

        source_uri = file_uri(source_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})

            foo_position = position_of(source_text, "foo", 1)
            generated = client.request("sail/generatedC", cursor_params(source_uri, foo_position))
            require(
                generated["uri"] == file_uri(target_generated_path),
                "manifest-paired sidecar resolved against wrong generated C output",
            )
            require(
                generated["range"]["start"] == {"line": 1, "character": 5},
                "manifest-paired generated C lookup used wrong target range",
            )

            print_ok("multi-manifest-c-pairing-smoke")
        finally:
            client.close()


def run_aggregate_artifact_index_smoke(sail_lsp):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-aggregate-artifacts-") as tempdir:
        build_a = os.path.join(tempdir, "build-a")
        build_b = os.path.join(tempdir, "build-b")
        os.mkdir(build_a)
        os.mkdir(build_b)

        source_path = os.path.join(tempdir, "model.sail")
        decoy_generated_path = os.path.join(build_a, "out.c")
        decoy_sidecar_path = os.path.join(build_a, "out.c.symbols.json")
        target_generated_path = os.path.join(build_b, "out.c")
        target_sidecar_path = os.path.join(build_b, "out.c.symbols.json")
        manifest_path = os.path.join(tempdir, "sail.lsp.json")

        source_text = "$include <prelude.sail>\n\nval foo : unit -> unit\n\nfunction foo() = ()\n"
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)
        with open(decoy_generated_path, "w", encoding="utf-8") as output:
            output.write("void zfoo(void) {}\n")
        with open(target_generated_path, "w", encoding="utf-8") as output:
            output.write("// aggregate target output\nvoid zfoo(void) {}\n")
        with open(decoy_sidecar_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.c.symbols",
                    "version": 2,
                    "symbols": [
                        {
                            "sailName": "decoy",
                            "cName": "zdecoy",
                            "kind": "function",
                            "generated": True,
                        }
                    ],
                },
                output,
            )
        with open(target_sidecar_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.c.symbols",
                    "version": 2,
                    "symbols": [
                        {
                            "sailName": "foo",
                            "cName": "zfoo",
                            "kind": "function",
                            "generated": True,
                        }
                    ],
                },
                output,
            )
        with open(manifest_path, "w", encoding="utf-8") as output:
            json.dump(
                {
                    "schema": "sail.lsp.artifacts",
                    "version": 1,
                    "artifacts": [
                        {
                            "cOutput": "build-a/out.c",
                            "cMap": "build-a/out.c.symbols.json",
                        },
                        {
                            "cOutput": "build-b/out.c",
                            "cMap": "build-b/out.c.symbols.json",
                        },
                    ],
                },
                output,
            )

        source_uri = file_uri(source_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})

            foo_position = position_of(source_text, "foo", 1)
            generated = client.request("sail/generatedC", cursor_params(source_uri, foo_position))
            require(
                generated["uri"] == file_uri(target_generated_path),
                "aggregate artifact index resolved against wrong generated C output",
            )
            require(
                generated["range"]["start"] == {"line": 1, "character": 5},
                "aggregate artifact index used wrong generated C range",
            )

            print_ok("aggregate-artifact-index-smoke")
        finally:
            client.close()


def run_compiler_type_smoke(sail_lsp):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-compiler-type-") as tempdir:
        source_path = os.path.join(tempdir, "model.sail")
        source_text = open(os.path.join(fixtures, "compiler_type.sail"), encoding="utf-8").read()
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)

        source_uri = file_uri(source_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})
            target_position = position_of(source_text, "= compiler_type_target()", 2)
            type_info = client.request("sail/type", cursor_params(source_uri, target_position))
            require(type_info["type"] == "unit -> unit", "compiler type lookup produced wrong type")
            require(type_info["source"] == "compiler", "type lookup did not use the compiler environment")

            local_position = position_of(source_text, "local_value\n}", 1)
            local_type = client.request("sail/type", cursor_params(source_uri, local_position))
            require(local_type["type"].startswith("int"), f"compiler local type lookup produced wrong type: {local_type}")
            require(local_type["source"] == "compiler", "local type lookup did not use the compiler AST")
            require(local_type["kind"] == "expression", "local type lookup did not report expression kind")

            local_references = client.request(
                "textDocument/references",
                {
                    "textDocument": {"uri": source_uri},
                    "position": local_position,
                    "context": {"includeDeclaration": True},
                },
            )
            require(len(local_references) == 2, "local references were not restricted to the enclosing function")
            require(
                all(reference["range"]["start"]["line"] in (15, 16) for reference in local_references),
                "local references leaked outside the enclosing function",
            )

            print_ok("compiler-type-smoke")
        finally:
            client.close()


def run_backend_sidecar_smoke(sail):
    source_path = os.path.join(repo_root, "test", "c", "bool_bits_mapping.sail")
    with tempfile.TemporaryDirectory(prefix="sail-lsp-sidecar-") as tempdir:
        out_prefix = os.path.join(tempdir, "bool_bits_mapping")
        result = subprocess.run(
            [sail, "--no-warn", "-c", "--c-emit-lsp-map", source_path, "-o", out_prefix],
            capture_output=True,
            text=True,
        )
        require(
            result.returncode == 0,
            f"C backend sidecar emission failed\nstdout:\n{result.stdout}\nstderr:\n{result.stderr}",
        )

        c_path = out_prefix + ".c"
        sidecar_path = c_path + ".symbols.json"
        index_path = out_prefix + ".sail_lsp.json"
        require(os.path.exists(c_path), "C backend did not emit C output")
        require(os.path.exists(sidecar_path), "C backend did not emit LSP sidecar")
        require(os.path.exists(index_path), "C backend did not emit LSP artifact index")

        sidecar = json.loads(open(sidecar_path, encoding="utf-8").read())
        require(sidecar.get("schema") == "sail.c.symbols", "sidecar schema marker missing")
        require(sidecar.get("version") == 2, "sidecar version missing")
        require(sidecar.get("language") == "c", "sidecar language missing")
        require(sidecar.get("cFile") == c_path, "sidecar cFile does not point at generated C")

        index = json.loads(open(index_path, encoding="utf-8").read())
        artifacts = index.get("artifacts", {})
        require(index.get("schema") == "sail.lsp.artifacts", "artifact index schema marker missing")
        require(index.get("version") == 1, "artifact index version missing")
        require(artifacts.get("cOutput") == os.path.realpath(c_path), "artifact index cOutput is wrong")
        require(artifacts.get("cMap") == os.path.realpath(sidecar_path), "artifact index cMap is wrong")

        symbols = sidecar.get("symbols", [])
        forwards = next(
            (symbol for symbol in symbols if symbol.get("sailName") == "bool_bits_forwards"),
            None,
        )
        require(forwards, "sidecar missing generated mapping helper")
        require(forwards.get("cName") == "zbool_bits_forwards", "sidecar emitted wrong C name")
        require(forwards.get("rangeStatus") == "resolved", "sidecar helper range was not resolved")
        require(forwards.get("cRange", {}).get("start", {}).get("line") is not None, "sidecar helper range missing")

        unresolved = [symbol for symbol in symbols if symbol.get("rangeStatus") == "missing"]
        require(
            all("cRange" not in symbol for symbol in unresolved),
            "unresolved sidecar entries should not include stale ranges",
        )
        print_ok("backend-sidecar-smoke")


def run_specialized_c_sidecar_smoke(sail_lsp, sail):
    source_fixture = os.path.join(repo_root, "test", "c", "special_annot.sail")
    with tempfile.TemporaryDirectory(prefix="sail-lsp-specialized-c-") as tempdir:
        source_path = os.path.join(tempdir, "special_annot.sail")
        shutil.copyfile(source_fixture, source_path)
        source_text = open(source_path, encoding="utf-8").read()
        source_uri = file_uri(source_path)
        out_prefix = os.path.join(tempdir, "out")

        result = subprocess.run(
            [
                sail,
                "--no-warn",
                "-c",
                "--c-emit-lsp-map",
                "--c-specialize",
                source_path,
                "-o",
                out_prefix,
            ],
            capture_output=True,
            text=True,
        )
        require(
            result.returncode == 0,
            f"specialized C sidecar emission failed\nstdout:\n{result.stdout}\nstderr:\n{result.stderr}",
        )

        c_path = out_prefix + ".c"
        sidecar_path = c_path + ".symbols.json"
        index_path = out_prefix + ".sail_lsp.json"
        require(os.path.exists(c_path), "specialized C backend did not emit C output")
        require(os.path.exists(sidecar_path), "specialized C backend did not emit sidecar")
        require(os.path.exists(index_path), "specialized C backend did not emit artifact index")

        sidecar = json.loads(open(sidecar_path, encoding="utf-8").read())
        symbols = sidecar.get("symbols", [])
        specialized = next((symbol for symbol in symbols if symbol.get("sailName") == "test<s>"), None)
        require(specialized, "specialized sidecar missing instantiated test<s> mapping")
        require(specialized.get("cName") == "ztestzIszK", "specialized sidecar emitted wrong C name")
        require(specialized.get("generated") is True, "specialized sidecar did not mark test<s> as generated")
        require(specialized.get("rangeStatus") == "resolved", "specialized sidecar range was not resolved")
        require(specialized.get("cRange", {}).get("start", {}).get("line") is not None, "specialized C range missing")

        index = json.loads(open(index_path, encoding="utf-8").read())
        require(index.get("schema") == "sail.lsp.artifacts", "specialized artifact index schema marker missing")
        require(index.get("artifacts", {}).get("cOutput") == os.path.realpath(c_path), "specialized index cOutput is wrong")
        require(index.get("artifacts", {}).get("cMap") == os.path.realpath(sidecar_path), "specialized index cMap is wrong")

        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "sail": sail,
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})

            call_position = position_of(source_text, 'test("string")', 1)
            definition = client.request("textDocument/definition", cursor_params(source_uri, call_position))
            definition_line = source_text.splitlines()[definition["range"]["start"]["line"]]
            require(
                definition["uri"] == source_uri and "function test" in definition_line,
                "specialized default definition did not resolve to Sail source",
            )

            cname = client.request("sail/cName", cursor_params(source_uri, call_position))
            require(cname["sailName"] == "test<s>", "specialized C name did not use sidecar instantiation")
            require(cname["cName"] == "ztestzIszK", "specialized C name response used wrong C symbol")
            require(cname["source"] == "sidecar", "specialized C name did not come from sidecar")

            generated_c = client.request("sail/generatedC", cursor_params(source_uri, call_position))
            require(generated_c["uri"] == file_uri(c_path), "specialized generated-C target used wrong file")
            require(
                generated_c["range"] == specialized["cRange"],
                "specialized generated-C target did not use sidecar range",
            )
            c_text = open(c_path, encoding="utf-8").read()
            c_line = c_text.splitlines()[generated_c["range"]["start"]["line"]]
            require("ztestzIszK" in c_line, "specialized generated-C target did not land on C function")

            print_ok("specialized-c-sidecar-smoke")
        finally:
            client.close()


def run_diagnostics_smoke(sail_lsp, sail):
    fail_path = os.path.join(repo_root, "test", "typecheck", "fail", "infer_if_error.sail")
    fail_text = open(fail_path, encoding="utf-8").read()
    fail_uri = file_uri(fail_path)

    client = LspClient([sail_lsp, "--stdio"])
    try:
        client.request(
            "initialize",
            {
                "rootUri": file_uri(repo_root),
                "initializationOptions": {
                    "sail": sail,
                    "diagnostics": True,
                },
            },
        )
        client.notify("textDocument/didOpen", {"textDocument": text_document(fail_uri, fail_text)})

        def has_expected_diagnostic(params):
            if params.get("uri") != fail_uri:
                return False
            return any("Could not infer type" in diagnostic.get("message", "") for diagnostic in params.get("diagnostics", []))

        diagnostics = client.wait_for_notification("textDocument/publishDiagnostics", has_expected_diagnostic, timeout=15.0)
        require(
            any(diagnostic.get("code") == "sail.type.infer" for diagnostic in diagnostics.get("diagnostics", [])),
            "diagnostic did not include structured inference code",
        )
        require(
            any(
                diagnostic.get("data", {}).get("origin") == "compiler"
                and diagnostic.get("data", {}).get("structured") is True
                for diagnostic in diagnostics.get("diagnostics", [])
            ),
            "diagnostic did not include compiler structured metadata",
        )

        mismatch_path = os.path.join(repo_root, "test", "typecheck", "fail", "non_bool_if.sail")
        mismatch_text = open(mismatch_path, encoding="utf-8").read()
        mismatch_uri = file_uri(mismatch_path)
        client.notify("textDocument/didOpen", {"textDocument": text_document(mismatch_uri, mismatch_text)})

        def has_mismatch_diagnostic(params):
            if params.get("uri") != mismatch_uri:
                return False
            return any(diagnostic.get("code") == "sail.type.mismatch" for diagnostic in params.get("diagnostics", []))

        client.wait_for_notification("textDocument/publishDiagnostics", has_mismatch_diagnostic, timeout=15.0)
        print_ok("diagnostics-smoke")
    finally:
        client.close()


def run_project_discovery_smoke(sail_lsp, sail):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-project-") as tempdir:
        source_path = os.path.join(tempdir, "model.sail")
        source_text = "$include <prelude.sail>\n\nval foo : unit -> unit\n\nfunction foo() = ()\n"
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)
        for name in ("a.sail_project", "b.sail_project"):
            with open(os.path.join(tempdir, name), "w", encoding="utf-8") as output:
                output.write("{}\n")

        source_uri = file_uri(source_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "sail": sail,
                        "diagnostics": True,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})

            def has_ambiguous_project(params):
                if params.get("uri") != source_uri:
                    return False
                return any(
                    diagnostic.get("code") == "sail.project.ambiguous"
                    for diagnostic in params.get("diagnostics", [])
                )

            diagnostic_params = client.wait_for_notification(
                "textDocument/publishDiagnostics", has_ambiguous_project, timeout=15.0
            )
            project_actions = client.request(
                "textDocument/codeAction",
                {
                    "textDocument": {"uri": source_uri},
                    "range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}},
                    "context": {"diagnostics": diagnostic_params.get("diagnostics", [])},
                },
            )
            require(
                any(action["title"] == "Sail: Choose Project File" for action in project_actions),
                "ambiguous project diagnostic did not offer project picker action",
            )
            print_ok("project-discovery-smoke")
        finally:
            client.close()


def run_code_action_edit_smoke(sail_lsp):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-actions-") as tempdir:
        source_path = os.path.join(tempdir, "model.sail")
        source_text = """$include <prelude.sail>

function lonely() = ()

function duplicate_binding() : unit -> unit = {
  let (x, x) = (true, false);
  ()
}
"""
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)

        source_uri = file_uri(source_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})
            lonely_position = position_of(source_text, "lonely")
            actions = client.request(
                "textDocument/codeAction",
                {
                    "textDocument": {"uri": source_uri},
                    "range": {"start": lonely_position, "end": lonely_position},
                    "context": {"diagnostics": []},
                },
            )
            insert_val = next((action for action in actions if action["title"] == "Sail: Insert Val Spec"), None)
            require(insert_val, "code actions missing edit-producing val spec action")
            edits = insert_val["edit"]["changes"][source_uri]
            require(edits[0]["newText"] == "val lonely : unit -> unit\n\n", "val spec action inserted wrong text")

            default_order_actions = client.request(
                "textDocument/codeAction",
                {
                    "textDocument": {"uri": source_uri},
                    "range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}},
                    "context": {
                        "diagnostics": [
                            {
                                "range": {
                                    "start": {"line": 0, "character": 0},
                                    "end": {"line": 0, "character": 1},
                                },
                                "code": "sail.order.default",
                                "message": "No default order has been set",
                            }
                        ]
                    },
                },
            )
            insert_default_order = next(
                (action for action in default_order_actions if action["title"] == "Sail: Insert Default Order"),
                None,
            )
            require(insert_default_order, "code actions missing default-order quick fix")
            default_order_edits = insert_default_order["edit"]["changes"][source_uri]
            require(
                default_order_edits[0]["newText"] == "default Order dec\n\n",
                "default-order action inserted wrong text",
            )

            duplicate_position = position_of(source_text, "x) =")
            duplicate_actions = client.request(
                "textDocument/codeAction",
                {
                    "textDocument": {"uri": source_uri},
                    "range": {"start": duplicate_position, "end": duplicate_position},
                    "context": {
                        "diagnostics": [
                            {
                                "range": {"start": duplicate_position, "end": duplicate_position},
                                "code": "sail.name.duplicateBinding",
                                "message": "Duplicate binding x",
                            }
                        ]
                    },
                },
            )
            rename_duplicate = next(
                (action for action in duplicate_actions if action["title"] == "Sail: Rename Duplicate Binding"),
                None,
            )
            require(rename_duplicate, "code actions missing duplicate-binding quick fix")
            duplicate_edits = rename_duplicate["edit"]["changes"][source_uri]
            require(duplicate_edits[0]["newText"] == "x_2", "duplicate-binding action inserted wrong text")
            require(
                duplicate_edits[0]["range"]["start"] == duplicate_position,
                "duplicate-binding action edited the wrong occurrence",
            )
            print_ok("code-action-edit-smoke")
        finally:
            client.close()


def run_reference_lexing_smoke(sail_lsp):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-reference-lexing-") as tempdir:
        source_path = os.path.join(tempdir, "model.sail")
        source_text = """default Order dec

$include <prelude.sail>

val foo : unit -> unit

function foo() = ()

val use_foo : unit -> unit

function use_foo() = {
  // foo in a line comment should not count
  /* foo in a block comment should not count */
  let ignored = "foo";
  foo()
}

val shadow_global : unit -> unit

function shadow_global() = ()

val use_shadow_global : unit -> int

function use_shadow_global() = {
  let shadow_global : int = 7;
  shadow_global
}

val call_shadow_global : unit -> unit

function call_shadow_global() = shadow_global()
"""
        with open(source_path, "w", encoding="utf-8") as output:
            output.write(source_text)

        source_uri = file_uri(source_path)
        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "diagnostics": False,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})
            call_position = position_of(source_text, "foo()\n}", 1)
            references = client.request(
                "textDocument/references",
                {
                    "textDocument": {"uri": source_uri},
                    "position": call_position,
                    "context": {"includeDeclaration": True},
                },
            )
            reference_lines = sorted(reference["range"]["start"]["line"] for reference in references)
            require(reference_lines == [4, 6, 14], f"references included comment/string matches: {reference_lines}")
            shadow_call_position = position_of(source_text, "shadow_global()\n", 1)
            shadow_references = client.request(
                "textDocument/references",
                {
                    "textDocument": {"uri": source_uri},
                    "position": shadow_call_position,
                    "context": {"includeDeclaration": True},
                },
            )
            shadow_reference_lines = sorted(reference["range"]["start"]["line"] for reference in shadow_references)
            require(
                shadow_reference_lines == [17, 19, 30],
                f"global references included local shadow matches: {shadow_reference_lines}",
            )
            local_completion_position = position_of(source_text, "  shadow_global\n}", 6)
            local_completions = client.request("textDocument/completion", cursor_params(source_uri, local_completion_position))
            shadow_completions = [
                item for item in local_completions["items"] if item["label"] == "shadow_global"
            ]
            require(len(shadow_completions) == 1, "local completion did not suppress shadowed top-level symbol")
            require(shadow_completions[0]["kind"] == 6, "local let completion did not advertise variable kind")
            require(shadow_completions[0]["detail"] == "local let", "local let completion used wrong detail")
            local_definition = client.request("textDocument/definition", cursor_params(source_uri, local_completion_position))
            local_definition_line = source_text.splitlines()[local_definition["range"]["start"]["line"]]
            require(
                local_definition["uri"] == source_uri and "let shadow_global" in local_definition_line,
                "local let definition did not resolve to local binder",
            )
            print_ok("reference-lexing-smoke")
        finally:
            client.close()


def run_architecture_fixture_smoke(sail_lsp, sail):
    with tempfile.TemporaryDirectory(prefix="sail-lsp-architecture-") as tempdir:
        source_fixture = os.path.join(repo_root, "test", "lean", "SailTinyArm.sail")
        source_path = os.path.join(tempdir, "SailTinyArm.sail")
        shutil.copyfile(source_fixture, source_path)
        source_text = open(source_path, encoding="utf-8").read()
        source_uri = file_uri(source_path)

        out_prefix = os.path.join(tempdir, "out")
        result = subprocess.run(
            [sail, "--no-warn", "-c", "--c-emit-lsp-map", source_path, "-o", out_prefix],
            capture_output=True,
            text=True,
        )
        require(
            result.returncode == 0,
            f"architecture C sidecar emission failed\nstdout:\n{result.stdout}\nstderr:\n{result.stderr}",
        )
        c_path = out_prefix + ".c"
        sidecar_path = c_path + ".symbols.json"
        index_path = out_prefix + ".sail_lsp.json"
        require(os.path.exists(c_path), "architecture fixture did not emit C output")
        require(os.path.exists(sidecar_path), "architecture fixture did not emit C sidecar")
        require(os.path.exists(index_path), "architecture fixture did not emit artifact index")
        sidecar = json.loads(open(sidecar_path, encoding="utf-8").read())
        require(sidecar.get("schema") == "sail.c.symbols", "architecture sidecar schema marker missing")
        require(sidecar.get("version") == 2, "architecture sidecar version missing")
        require(sidecar.get("language") == "c", "architecture sidecar language missing")
        index = json.loads(open(index_path, encoding="utf-8").read())
        require(index.get("schema") == "sail.lsp.artifacts", "architecture artifact index schema marker missing")
        require(index.get("artifacts", {}).get("cOutput") == os.path.realpath(c_path), "architecture index cOutput is wrong")
        require(index.get("artifacts", {}).get("cMap") == os.path.realpath(sidecar_path), "architecture index cMap is wrong")
        sidecar_symbols = sidecar.get("symbols", [])
        require(len(sidecar_symbols) >= 50, "architecture sidecar unexpectedly small")
        resolved_symbols = [
            symbol for symbol in sidecar_symbols if symbol.get("rangeStatus") == "resolved" and "cRange" in symbol
        ]
        require(len(resolved_symbols) >= 40, "architecture sidecar resolved too few generated ranges")
        rmem_symbol = next((symbol for symbol in sidecar_symbols if symbol.get("sailName") == "rMem"), None)
        require(rmem_symbol, "architecture sidecar missing rMem mapping")
        require(rmem_symbol.get("cName") == "zrMem", "architecture sidecar emitted wrong rMem C name")
        require(rmem_symbol.get("generated") is True, "architecture sidecar did not mark rMem as generated")
        require(rmem_symbol.get("rangeStatus") == "resolved", "architecture sidecar did not resolve rMem range")
        require(rmem_symbol.get("cRange", {}).get("start", {}).get("line") is not None, "rMem sidecar range missing")

        client = LspClient([sail_lsp, "--stdio"])
        try:
            client.request(
                "initialize",
                {
                    "rootUri": file_uri(tempdir),
                    "initializationOptions": {
                        "sail": sail,
                        "diagnostics": True,
                    },
                },
            )
            client.notify("textDocument/didOpen", {"textDocument": text_document(source_uri, source_text)})
            architecture_diagnostics = client.wait_for_notification(
                "textDocument/publishDiagnostics",
                lambda params: params.get("uri") == source_uri,
                timeout=20.0,
            )
            architecture_diagnostic_list = architecture_diagnostics.get("diagnostics", [])
            require(
                architecture_diagnostic_list
                and all(diagnostic.get("severity") == 2 for diagnostic in architecture_diagnostic_list),
                f"architecture fixture diagnostics were not warnings: {architecture_diagnostic_list}",
            )
            require(
                any(
                    diagnostic.get("code") == "sail.warning"
                    and "Unused variable" in diagnostic.get("message", "")
                    for diagnostic in architecture_diagnostic_list
                ),
                "architecture fixture did not surface compiler warning diagnostics",
            )

            symbols = client.request("textDocument/documentSymbol", {"textDocument": {"uri": source_uri}})
            symbol_names = {symbol["name"] for symbol in symbols}
            require("fetch_and_execute" in symbol_names, "architecture fixture missing function symbol")
            require("_PC" in symbol_names, "architecture fixture missing register symbol")
            require("AccessDescriptor" in symbol_names, "architecture fixture missing struct symbol")

            source_map = client.request("sail/sourceMap", {"textDocument": {"uri": source_uri}})
            mapped_names = {entry["name"]: entry for entry in source_map}
            require(len(source_map) >= 100, "architecture source map unexpectedly small")
            require(mapped_names["fetch_and_execute"]["kind"] == "function", "source map lost function kind")
            require(mapped_names["_PC"]["kind"] == "register", "source map lost register kind")
            require(mapped_names["AccessDescriptor"]["kind"] == "struct", "source map lost struct kind")

            workspace_symbols = client.request("workspace/symbol", {"query": "fetch"})
            require(
                any(symbol["name"] == "fetch_and_execute" for symbol in workspace_symbols),
                "workspace symbols missing architecture function",
            )

            call_position = position_of(source_text, "rMem(addr)", 1)
            definition = client.request("textDocument/definition", cursor_params(source_uri, call_position))
            definition_line = source_text.splitlines()[definition["range"]["start"]["line"]]
            require(
                definition["uri"] == source_uri and "function rMem" in definition_line,
                "architecture fixture definition did not resolve to Sail function",
            )

            generated_c = client.request("sail/generatedC", cursor_params(source_uri, call_position))
            require(generated_c["uri"] == file_uri(c_path), "architecture generated-C target used wrong file")
            require(
                generated_c["range"] == rmem_symbol["cRange"],
                "architecture generated-C target did not use sidecar range",
            )

            semantic_tokens = client.request(
                "textDocument/semanticTokens/full",
                {"textDocument": {"uri": source_uri}},
            )
            require(len(semantic_tokens.get("data", [])) > 200, "architecture semantic tokens unexpectedly small")
            print_ok("architecture-fixture-smoke")
        finally:
            client.close()


def main():
    banner("Testing Sail LSP")
    sail_lsp = resolve_tool("SAIL_LSP", "sail_lsp", os.path.join("_build", "default", "src", "bin", "sail_lsp.exe"))
    sail = resolve_tool("SAIL", "sail", "sail")

    run_navigation_smoke(sail_lsp)
    run_source_documentation_smoke(sail_lsp)
    run_c_artifact_discovery_smoke(sail_lsp)
    run_artifact_index_smoke(sail_lsp, sail)
    run_watched_sidecar_refresh_smoke(sail_lsp)
    run_watched_diagnostics_refresh_smoke(sail_lsp, sail)
    run_recursive_artifact_index_smoke(sail_lsp)
    run_multi_manifest_c_pairing_smoke(sail_lsp)
    run_aggregate_artifact_index_smoke(sail_lsp)
    run_compiler_type_smoke(sail_lsp)
    run_backend_sidecar_smoke(sail)
    run_specialized_c_sidecar_smoke(sail_lsp, sail)
    run_diagnostics_smoke(sail_lsp, sail)
    run_project_discovery_smoke(sail_lsp, sail)
    run_code_action_edit_smoke(sail_lsp)
    run_reference_lexing_smoke(sail_lsp)
    run_architecture_fixture_smoke(sail_lsp, sail)

    with open("tests.xml", "w", encoding="utf-8") as output:
        output.write(
            '<testsuites>\n  <testsuite name="lsp" tests="17" failures="0">\n'
            '    <testcase name="navigation-smoke"/>\n'
            '    <testcase name="source-documentation-smoke"/>\n'
            '    <testcase name="c-artifact-discovery-smoke"/>\n'
            '    <testcase name="artifact-index-smoke"/>\n'
            '    <testcase name="watched-sidecar-refresh-smoke"/>\n'
            '    <testcase name="watched-diagnostics-refresh-smoke"/>\n'
            '    <testcase name="recursive-artifact-index-smoke"/>\n'
            '    <testcase name="multi-manifest-c-pairing-smoke"/>\n'
            '    <testcase name="aggregate-artifact-index-smoke"/>\n'
            '    <testcase name="compiler-type-smoke"/>\n'
            '    <testcase name="backend-sidecar-smoke"/>\n'
            '    <testcase name="specialized-c-sidecar-smoke"/>\n'
            '    <testcase name="diagnostics-smoke"/>\n'
            '    <testcase name="project-discovery-smoke"/>\n'
            '    <testcase name="code-action-edit-smoke"/>\n'
            '    <testcase name="reference-lexing-smoke"/>\n'
            '    <testcase name="architecture-fixture-smoke"/>\n'
            "  </testsuite>\n</testsuites>\n"
        )


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(f"{color.FAIL}LSP tests failed: {exc}{color.END}")
        sys.exit(1)
