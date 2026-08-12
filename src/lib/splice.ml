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

(* Currently limited to:
   - functions and non-scattered type definitions, no preprocessor
   - no new undefined functions (but no explicit check here yet)
*)

open Ast
open Ast_compare
open Ast_defs
open Ast_util

let scan_ast { defs; _ } =
  let scan (ids, specs, type_defs) (DEF_aux (aux, def_annot) as def) =
    match aux with
    | DEF_fundef fd -> (IdSet.add (id_of_fundef fd) ids, specs, type_defs)
    | DEF_val (VS_aux (VS_val_spec (_, id, _), _) as vs) -> (ids, Bindings.add id (vs, def_annot) specs, type_defs)
    | DEF_type td -> (ids, specs, Bindings.add (id_of_type_def td) def type_defs)
    | DEF_pragma (("file_start" | "file_end"), _) -> (ids, specs, type_defs)
    | _ ->
        raise
          (Reporting.err_general (def_loc def) "Definition in splice file isn't a spec, function, or type definition")
  in
  List.fold_left scan (IdSet.empty, Bindings.empty, Bindings.empty) defs

let filter_old_ast repl_ids repl_specs repl_types repl_undefined_ids { defs; _ } =
  let check (rdefs, specs_found, types_found) (DEF_aux (aux, def_annot) as def) =
    match aux with
    | DEF_fundef fd ->
        let id = id_of_fundef fd in
        if IdSet.mem id repl_undefined_ids then (rdefs, specs_found, types_found)
        else if IdSet.mem id repl_ids then
          ( DEF_aux (DEF_pragma ("spliced_function#", Pragma_line (string_of_id id, def_annot.loc)), def_annot) :: rdefs,
            specs_found,
            types_found
          )
        else (def :: rdefs, specs_found, types_found)
    | DEF_val (VS_aux (VS_val_spec (_, id, _), _)) ->
        if IdSet.mem id repl_undefined_ids then (rdefs, specs_found, types_found)
        else (
          match Bindings.find_opt id repl_specs with
          (* Keep the replacement's def_annot so attribute-only val splices
           (e.g. $[c_inline] on a spec-defined function) survive, mirroring
           how replacement type definitions already retain their attributes. *)
          | Some (vs, repl_annot) ->
              ( DEF_aux (DEF_val vs, { repl_annot with loc = def_annot.loc }) :: rdefs,
                IdSet.add id specs_found,
                types_found
              )
          | None -> (def :: rdefs, specs_found, types_found)
        )
    | DEF_type td -> (
        let id = id_of_type_def td in
        match Bindings.find_opt id repl_types with
        | Some (DEF_aux (repl_aux, repl_annot)) ->
            (DEF_aux (repl_aux, { repl_annot with loc = def_annot.loc }) :: rdefs, specs_found, IdSet.add id types_found)
        | None -> (def :: rdefs, specs_found, types_found)
      )
    | _ -> (def :: rdefs, specs_found, types_found)
  in
  let rdefs, specs_found, types_found = List.fold_left check ([], IdSet.empty, IdSet.empty) defs in
  (List.rev rdefs, specs_found, types_found)

let filter_replacements specs_found types_found { defs; _ } =
  let not_found = function
    | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, id, _), _)), _) -> not (IdSet.mem id specs_found)
    | DEF_aux (DEF_type td, _) -> not (IdSet.mem (id_of_type_def td) types_found)
    | _ -> true
  in
  List.filter not_found defs

let move_replacement_fundefs ast =
  let rec aux acc = function
    | DEF_aux (DEF_pragma ("spliced_function#", Pragma_line (id, original_loc)), _) :: defs ->
        let is_replacement = function
          | DEF_aux (DEF_fundef fd, _) -> string_of_id (id_of_fundef fd) = id
          | _ -> false
        in
        let replacement, other_defs = List.partition is_replacement defs in
        let replacement =
          List.map
            (function DEF_aux (repl_aux, repl_annot) -> DEF_aux (repl_aux, { repl_annot with loc = original_loc }))
            replacement
        in
        aux (replacement @ acc) other_defs
    | def :: defs -> aux (def :: acc) defs
    | [] -> List.rev acc
  in
  { ast with defs = aux [] ast.defs }

let annotate_ast ast =
  let annotate_def (DEF_aux (d, a)) =
    DEF_aux (d, add_def_attribute a.loc "spliced" None a)
    |> map_def_def_annot (def_annot_map_env (fun _ -> Type_check.Env.empty))
  in
  { ast with defs = List.map annotate_def ast.defs }

let splice ctx ast file =
  let parsed_ast = Initial_check.parse_file file |> snd in
  let repl_ast, _ = Initial_check.process_ast ctx (Parse_ast.Defs [(Some file, parsed_ast)]) in
  let repl_ast = map_ast_annot (fun (l, _) -> (l, Type_check.empty_tannot)) repl_ast in
  let repl_ast = annotate_ast repl_ast in
  let repl_ids, repl_specs, repl_types = scan_ast repl_ast in
  let repl_undefined_ids =
    Bindings.fold
      (fun id def ids ->
        match def with
        | DEF_aux (DEF_type (TD_aux ((TD_record _ | TD_enum _), _)), _) -> IdSet.add (prepend_id "undefined_" id) ids
        | _ -> ids
      )
      repl_types IdSet.empty
  in
  let defs1, specs_found, types_found = filter_old_ast repl_ids repl_specs repl_types repl_undefined_ids ast in
  let defs2 = filter_replacements specs_found types_found repl_ast in
  { ast with defs = defs1 @ defs2 }

let splice_files ctx env ast files =
  let spliced_ast = List.fold_left (fun ast file -> splice ctx ast file) ast files in
  let checked_ast, checked_env = Type_error.check Type_check.initial_env (Type_check.strip_ast spliced_ast) in
  let checked_env =
    match Type_check.Env.get_modules env with
    | Some project -> Type_check.Env.set_modules project checked_env
    | None -> checked_env
  in
  (* Move replacement functions into place and top-sort, in case dependencies have changed *)
  let sorted_ast = Callgraph.top_sort_defs (move_replacement_fundefs checked_ast) in
  (sorted_ast, checked_env)
