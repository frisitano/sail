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

open Ast
open Ast_compare
open Ast_defs
open Ast_util
open Bit
open Parse_ast.Attribute_data
open Jib
open Jib_util
open Jib_visitor
open Type_check
open Value2
module Document = Pretty_print_sail.Document

open Anf

let opt_memo_cache = ref false

(* Representation specialization can be expensive on large models. Keep its
   progress trace opt-in so ordinary backends remain quiet while allowing the
   C backend to expose actionable worklist and bound progress. *)
let opt_debug_function_representations = ref false
let opt_lint_readability = ref false

type representation_specialization = {
  source_id : id;
  specialized_id : id;
  source_location : Ast.l;
  semantic_parameters : ctyp list;
  represented_parameters : ctyp list;
  semantic_result : ctyp;
  represented_result : ctyp;
  argument_bounds : (Big_int.num * Big_int.num) option list;
  result_bound : (Big_int.num * Big_int.num) option;
  calls : (id * ctyp list * ctyp * bool) list;
  conversions : (ctyp * ctyp * bool) list;
  recursive : bool;
}

let representation_specializations = ref []
let reset_representation_specializations () = representation_specializations := []

(* A proof partition is never weakened merely to satisfy this limit.  Hitting
   the budget is an explicit extraction error, so callers either receive the
   specialization justified by their semantic facts or compilation stops. *)
let opt_max_function_specializations = ref 64

let rec jib_source_loc = function
  | Parse_ast.Generated l | Parse_ast.Unique (_, l) -> jib_source_loc l
  | Parse_ast.Hint (_, primary, fallback) -> (
      match jib_source_loc primary with Parse_ast.Unknown -> jib_source_loc fallback | l -> l
    )
  | l -> l

type jib_readability_finding = { rule : string; location : Parse_ast.l; message : string }

let report_jib_readability_finding finding =
  match jib_source_loc finding.location with
  | Parse_ast.Unknown -> ()
  | l -> Reporting.warn ("Jib readability lint [" ^ finding.rule ^ "]") l finding.message

let same_name lhs rhs = Name.compare lhs rhs = 0

let rec cval_read_count name = function
  | V_id (id, _) -> if same_name name id then 1 else 0
  | V_lit _ | V_member _ -> 0
  | V_field (value, _, _) | V_tuple_member (value, _, _) | V_ctor_kind (value, _) | V_ctor_unwrap (value, _, _) ->
      cval_read_count name value
  | V_call (_, values) | V_tuple values ->
      List.fold_left (fun count value -> count + cval_read_count name value) 0 values
  | V_struct (fields, _) -> List.fold_left (fun count (_, value) -> count + cval_read_count name value) 0 fields

let init_read_count name = function
  | Init_cval value -> cval_read_count name value
  | Init_static _ | Init_json_key _ -> 0

let rec clexp_read_count name = function
  | CL_id _ | CL_void _ -> 0
  | CL_rmw (read, _, _) -> if same_name name read then 1 else 0
  | CL_field (lexp, _, _) | CL_tuple (lexp, _) | CL_addr lexp -> clexp_read_count name lexp

let creturn_read_count name = function
  | CR_one lexp -> clexp_read_count name lexp
  | CR_multi lexps -> List.fold_left (fun count lexp -> count + clexp_read_count name lexp) 0 lexps

let rec instr_read_count name (I_aux (instr, _)) =
  match instr with
  | I_decl _ | I_clear _ | I_undefined _ | I_exit _ | I_comment _ | I_raw _ | I_label _ | I_goto _ | I_reset _ -> 0
  | I_init (_, _, init) -> init_read_count name init
  | I_jump (value, _) | I_throw value | I_return value | I_reinit (_, _, value) -> cval_read_count name value
  | I_funcall (returns, _, _, args) ->
      creturn_read_count name returns + List.fold_left (fun count value -> count + cval_read_count name value) 0 args
  | I_copy (lexp, value) -> clexp_read_count name lexp + cval_read_count name value
  | I_end id -> if same_name name id then 1 else 0
  | I_if (condition, then_instrs, else_instrs) ->
      cval_read_count name condition + instrs_read_count name then_instrs + instrs_read_count name else_instrs
  | I_block instrs | I_try_block instrs -> instrs_read_count name instrs

and instrs_read_count name instrs = List.fold_left (fun count instr -> count + instr_read_count name instr) 0 instrs

let is_generated_temporary = function Gen _ -> true | _ -> false

let is_bool_literal = function V_lit (VL_bool _, CT_bool) -> true | _ -> false

let rec lint_jib_cval warn l value =
  ( match value with
  | V_call (Bnot, [V_lit (VL_bool _, CT_bool)]) ->
      warn "jib-redundant-bool" l "Lowering retained a negation of a boolean literal."
  | V_call (Bnot, [V_call (Bnot, [_])]) -> warn "jib-redundant-bool" l "Lowering retained a double boolean negation."
  | V_call ((Eq | Neq), [lhs; rhs]) when is_bool_literal lhs || is_bool_literal rhs ->
      warn "jib-redundant-bool" l "Lowering retained a boolean comparison with a boolean literal."
  | _ -> ()
  );
  match value with
  | V_field (value, _, _) | V_tuple_member (value, _, _) | V_ctor_kind (value, _) | V_ctor_unwrap (value, _, _) ->
      lint_jib_cval warn l value
  | V_call (_, values) | V_tuple values -> List.iter (lint_jib_cval warn l) values
  | V_struct (fields, _) -> List.iter (fun (_, value) -> lint_jib_cval warn l value) fields
  | V_id _ | V_lit _ | V_member _ -> ()

let lint_jib_instr_cvals warn l = function
  | I_init (_, _, Init_cval value) | I_reinit (_, _, value) | I_jump (value, _) | I_throw value | I_return value ->
      lint_jib_cval warn l value
  | I_funcall (_, _, _, args) -> List.iter (lint_jib_cval warn l) args
  | I_copy (_, value) -> lint_jib_cval warn l value
  | I_if (condition, _, _) -> lint_jib_cval warn l condition
  | I_decl _
  | I_init (_, _, (Init_static _ | Init_json_key _))
  | I_clear _ | I_undefined _ | I_exit _ | I_comment _ | I_raw _ | I_label _ | I_goto _ | I_reset _ | I_end _
  | I_block _ | I_try_block _ ->
      ()

let rec collect_jump_targets targets (I_aux (instr, _)) =
  match instr with
  | I_jump (_, label) | I_goto label -> Util.StringSet.add label targets
  | I_if (_, then_instrs, else_instrs) ->
      List.fold_left collect_jump_targets (List.fold_left collect_jump_targets targets then_instrs) else_instrs
  | I_block instrs | I_try_block instrs -> List.fold_left collect_jump_targets targets instrs
  | _ -> targets

let rec erase_jib_instruction_locations (I_aux (instr, _)) =
  let instr =
    match instr with
    | I_if (condition, then_instrs, else_instrs) ->
        I_if
          ( condition,
            List.map erase_jib_instruction_locations then_instrs,
            List.map erase_jib_instruction_locations else_instrs
          )
    | I_block instrs -> I_block (List.map erase_jib_instruction_locations instrs)
    | I_try_block instrs -> I_try_block (List.map erase_jib_instruction_locations instrs)
    | instr -> instr
  in
  I_aux (instr, (0, Parse_ast.Unknown))

let instruction_sequences_equal lhs rhs =
  List.compare Stdlib.compare
    (List.map erase_jib_instruction_locations lhs)
    (List.map erase_jib_instruction_locations rhs)
  = 0

let clexps_equal lhs rhs = Stdlib.compare lhs rhs = 0

let rec instruction_sequence_terminates = function
  | [] -> false
  | instrs -> (
      match List.hd (List.rev instrs) with
      | I_aux ((I_return _ | I_throw _ | I_exit _), _) -> true
      | I_aux ((I_block nested | I_try_block nested), _) -> instruction_sequence_terminates nested
      | I_aux (I_if (_, then_instrs, else_instrs), _) ->
          instruction_sequence_terminates then_instrs && instruction_sequence_terminates else_instrs
      | _ -> false
    )

let instruction_sequence_writes name instrs = List.exists (instr_references ~write:name ~direct:false) instrs

let jib_readability_findings instrs =
  let findings = ref [] in
  let warn rule location message = findings := { rule; location; message } :: !findings in
  let targets = List.fold_left collect_jump_targets Util.StringSet.empty instrs in
  let rec scan_sequence instrs =
    ( match instrs with
    | I_aux (I_decl (_, name), (_, l)) :: I_aux (I_if (_, then_instrs, else_instrs), _) :: I_aux (next, _) :: _ ->
        let then_writes = instruction_sequence_writes name then_instrs in
        let else_writes = instruction_sequence_writes name else_instrs in
        let missing_branch_falls_through =
          if then_writes then not (instruction_sequence_terminates else_instrs)
          else not (instruction_sequence_terminates then_instrs)
        in
        if
          Bool.compare then_writes else_writes <> 0
          && missing_branch_falls_through
          && instr_read_count name (I_aux (next, (0, Parse_ast.Unknown))) > 0
        then
          warn "jib-partial-branch-initialization" l "A local is read after only one fallthrough branch initializes it."
    | I_aux (I_decl (ctyp, declared), (_, l)) :: I_aux (next, _) :: _ ->
        let assigned =
          match next with
          | I_copy (CL_id (destination, _), _) -> same_name declared destination
          | I_funcall (CR_one (CL_id (destination, _)), _, _, _) -> same_name declared destination
          | _ -> false
        in
        if assigned then
          warn "jib-declaration-assignment-split" l
            "Lowering separated a local declaration from its immediate initialization.";
        if ctyp = CT_unit then
          warn "jib-unit-plumbing" l "Lowering introduced a unit-valued local that a backend can erase."
    | I_aux (I_decl (CT_unit, _), (_, l)) :: _ ->
        warn "jib-unit-plumbing" l "Lowering introduced a unit-valued local that a backend can erase."
    | I_aux (I_init (_, name, Init_cval _), (_, l)) :: rest
      when is_generated_temporary name && instrs_read_count name rest = 1 ->
        let is_rewritten = List.exists (instr_references ~write:name ~direct:false) rest in
        if not is_rewritten then
          warn "jib-single-use-pure-temporary" l
            "Lowering introduced a single-use pure temporary that can be inlined without reordering effects."
    | I_aux (I_init (_, name, Init_cval _), (_, l)) :: rest
      when is_generated_temporary name && instrs_read_count name rest = 0 ->
        let is_rewritten = List.exists (instr_references ~write:name ~direct:false) rest in
        if not is_rewritten then
          warn "jib-dead-pure-temporary" l
            "Lowering introduced an unread pure temporary that can be removed without reordering effects."
    | I_aux (I_goto target, (_, l)) :: I_aux (I_label label, _) :: _ when String.equal target label ->
        warn "jib-redundant-join" l "A jump to the immediately following label is redundant."
    | _ -> ()
    );
    match instrs with _ :: rest -> scan_sequence rest | [] -> ()
  in
  let rec scan instrs =
    scan_sequence instrs;
    List.iter
      (fun (I_aux (instr, (_, l))) ->
        lint_jib_instr_cvals warn l instr;
        ( match instr with
        | I_block ([] | [_]) | I_try_block ([] | [_]) ->
            warn "jib-redundant-scope" l "Lowering introduced an empty or single-instruction block."
        | I_if (V_lit (VL_bool _, CT_bool), _, _) ->
            warn "jib-constant-conditional" l "Lowering retained a conditional with a constant condition."
        | I_if (_, [], []) ->
            warn "jib-empty-conditional" l "Lowering retained a conditional whose branches are both empty."
        | I_if (_, then_instrs, else_instrs)
          when then_instrs <> [] && instruction_sequences_equal then_instrs else_instrs ->
            warn "jib-duplicate-branches" l
              "Lowering retained identical conditional branches; keep the shared body once."
        | I_if (_, [I_aux (I_copy (then_destination, _), _)], [I_aux (I_copy (else_destination, _), _)])
          when clexps_equal then_destination else_destination ->
            warn "jib-conditional-assignment" l
              "Both branches assign pure values to the same destination; a value-selecting backend can emit one \
               conditional assignment."
        | I_if (_, then_instrs, _ :: _) when instruction_sequence_terminates then_instrs ->
            warn "jib-else-after-terminal" l "Lowering retained an else branch after a terminal return, throw, or exit."
        | I_copy (CL_id (destination, _), V_id (source, _)) when same_name destination source ->
            warn "jib-identity-copy" l "Lowering introduced a local self-copy."
        | I_return (V_lit (VL_unit, CT_unit)) ->
            warn "jib-unit-plumbing" l
              "Lowering retained an explicit unit return that void-returning backends can erase."
        | I_label label when not (Util.StringSet.mem label targets) ->
            warn "jib-dead-label" l "Lowering introduced a label with no incoming jump."
        | I_decl (_, Gen (_, _, _, None, _)) | I_init (_, Gen (_, _, _, None, _), _) ->
            warn "jib-lost-source-name" l "A generated local has no retained Sail source-name provenance."
        | _ -> ()
        );
        match instr with
        | I_if (_, then_instrs, else_instrs) ->
            scan then_instrs;
            scan else_instrs
        | I_block nested | I_try_block nested -> scan nested
        | _ -> ()
      )
      instrs
  in
  scan instrs;
  List.rev !findings

let lint_jib_cdefs cdefs =
  List.iter
    (function
      | CDEF_aux
          ( ( CDEF_register (_, _, instrs)
            | CDEF_let (_, _, instrs)
            | CDEF_fundef (_, _, _, instrs)
            | CDEF_startup (_, instrs)
            | CDEF_finish (_, instrs) ),
            _
          ) ->
          List.iter report_jib_readability_finding (jib_readability_findings instrs)
      | _ -> ()
      )
    cdefs

let optimize_aarch64_fast_struct = ref false

let ngensym = symbol_generator ()

type funwire = Arg of int | Ret | Invoke

(**************************************************************************)
(* 4. Conversion to low-level AST                                         *)
(**************************************************************************)

(** We now use a low-level AST called Jib (see language/bytecode.ott) that is only slightly abstracted away from C. To
    be succint in comments we usually refer to this as Sail IR or IR rather than low-level AST repeatedly.

    The general idea is ANF expressions are converted into lists of instructions (type instr) where allocations and
    deallocations are now made explicit. ANF values (aval) are mapped to the cval type, which is even simpler still.
    Some things are still more abstract than in C, so the type definitions follow the sail type definition structure,
    just with typ (from ast.ml) replaced with ctyp. Top-level declarations that have no meaning for the backend are not
    included at this level.

    The convention used here is that functions of the form compile_X compile the type X into types in this AST, so
    compile_aval maps avals into cvals. Note that the return types for these functions are often quite complex, and they
    usually return some tuple containing setup instructions (to allocate memory for the expression), cleanup
    instructions (to deallocate that memory) and possibly typing information about what has been translated. **)

(* FIXME: This stage shouldn't care about this *)
let max_int n = Big_int.pred (Big_int.pow_int_positive 2 (n - 1))
let min_int n = Big_int.negate (Big_int.pow_int_positive 2 (n - 1))

(* A foreach loop is mathematical-integer code in the Sail source.  Keep that
   representation unless the source types prove both the loop values and the
   final (post-body) cursor update fit in int64_t.  The latter matters because
   an inclusive loop still computes [to + step] (or [to - step]) after its
   final body execution. *)
let foreach_int64_proven env from_typ to_typ step_typ ord =
  let add_bounds (env, bounds) typ =
    let typ = Env.expand_synonyms env typ in
    match destruct_range Env.empty typ with
    | Some (kids, constr, lower, upper) ->
        let env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr env in
        Some (env, (lower, upper) :: bounds)
    | None -> None
  in
  match
    Option.bind
      (add_bounds (env, []) from_typ)
      (fun state -> Option.bind (add_bounds state to_typ) (fun state -> add_bounds state step_typ))
  with
  | Some (env, [(step_lower, step_upper); (to_lower, to_upper); (from_lower, from_upper)]) -> (
      let int64_min = nconstant (min_int 64) in
      let int64_max = nconstant (max_int 64) in
      let zero = nconstant Big_int.zero in
      let fits (lower, upper) =
        prove __POS__ env (nc_lteq int64_min lower) && prove __POS__ env (nc_lteq upper int64_max)
      in
      fits (from_lower, from_upper)
      && fits (to_lower, to_upper)
      && fits (step_lower, step_upper)
      && prove __POS__ env (nc_lteq zero step_lower)
      &&
      match ord with
      | Ord_inc -> prove __POS__ env (nc_lteq (nexp_simp (nsum to_upper step_upper)) int64_max)
      | Ord_dec -> prove __POS__ env (nc_lteq int64_min (nexp_simp (nminus to_lower step_upper)))
    )
  | _ -> false

let is_ct_enum = function CT_enum _ -> true | _ -> false

let iblock1 = function [instr] -> instr | instrs -> iblock instrs

type abstract_type_initialised = Initialised | Uninitialised

type generic_signature = { generic_parameters : KidSet.t list; generic_result : KidSet.t }

(** The context type contains two type-checking environments. ctx.local_env contains the closest typechecking
    environment, usually from the expression we are compiling, whereas ctx.tc_env is the global type checking
    environment from type-checking the entire AST. We also keep track of local variables in ctx.locals, so we know when
    their type changes due to flow typing. *)
type ctx = {
  target_name : string;
  records : (kid list * ctyp Bindings.t) Bindings.t;
  enums : IdSet.t Bindings.t;
  variants : (kid list * ctyp Bindings.t) Bindings.t;
  abstracts : (ctyp * abstract_type_initialised) Bindings.t;
  valspecs : (string option * ctyp list * ctyp * uannot) Bindings.t;
  generic_signatures : generic_signature Bindings.t;
  quants : ctyp KBindings.t;
  local_env : Env.t;
  tc_env : Env.t;
  effect_info : Effects.side_effect_info;
  locals : (mut * ctyp) NameMap.t;
  registers : ctyp Bindings.t;
  letbinds : int list;
  letbind_ctyps : ctyp Bindings.t;
  no_raw : bool;
  no_static : bool;
  coverage_override : bool;
  def_annot : unit def_annot option;
}

let letbind_ids ctx =
  List.fold_left (fun ids (id, _) -> NameSet.add (name id) ids) NameSet.empty (Bindings.bindings ctx.letbind_ctyps)

let ctx_map_ctyps f ctx =
  {
    ctx with
    records = Bindings.map (fun (params, fields) -> (params, Bindings.map f fields)) ctx.records;
    variants = Bindings.map (fun (params, fields) -> (params, Bindings.map f fields)) ctx.variants;
    abstracts = Bindings.map (fun (ctyp, initialised) -> (f ctyp, initialised)) ctx.abstracts;
    valspecs =
      Bindings.map
        (fun (extern, param_ctyps, ret_ctyp, uannot) -> (extern, List.map f param_ctyps, f ret_ctyp, uannot))
        ctx.valspecs;
  }

let ctx_is_extern id ctx =
  match Bindings.find_opt id ctx.valspecs with
  | Some (Some _, _, _, _) -> true
  | Some (None, _, _, _) -> false
  | None -> Env.is_extern id ctx.tc_env ctx.target_name

let ctx_get_extern id ctx =
  match Bindings.find_opt id ctx.valspecs with
  | Some (Some extern, _, _, _) -> extern
  | Some (None, _, _, _) ->
      Reporting.unreachable (id_loc id) __POS__
        ("Tried to get extern information for non-extern function " ^ string_of_id id)
  | None -> Env.get_extern id ctx.tc_env ctx.target_name

let ctx_has_val_spec id ctx = Bindings.mem id ctx.valspecs || Bindings.mem id (Env.get_val_specs ctx.tc_env)

let initial_ctx ?for_target env effect_info =
  let initial_valspecs =
    [
      (mk_id "size_itself_int", (Some "size_itself_int", [CT_lint], CT_lint, empty_uannot));
      (mk_id "make_the_value", (Some "make_the_value", [CT_lint], CT_lint, empty_uannot));
    ]
    |> List.to_seq |> Bindings.of_seq
  in
  let target_name =
    match for_target with
    | Some name -> name
    | None -> Option.map Target.name (Target.get_the_target ()) |> Option.value ~default:"c"
  in
  {
    target_name;
    records = Bindings.empty;
    enums = Bindings.empty;
    variants = Bindings.empty;
    abstracts = Bindings.empty;
    valspecs = initial_valspecs;
    generic_signatures = Bindings.empty;
    quants = KBindings.empty;
    local_env = env;
    tc_env = env;
    effect_info;
    locals = NameMap.empty;
    registers = Bindings.empty;
    letbinds = [];
    letbind_ctyps = Bindings.empty;
    no_raw = false;
    no_static = false;
    coverage_override = true;
    def_annot = None;
  }

let instantiate_polymorphic_type ~at:l typ_id ctyps type_info =
  match Bindings.find_opt typ_id type_info with
  | None -> Reporting.unreachable l __POS__ ("Attempted to instantiate unknown type " ^ string_of_id typ_id)
  | Some (params, constructors) ->
      if List.compare_lengths ctyps params <> 0 then
        Reporting.unreachable l __POS__ ("Incorrect number of arguments for type " ^ string_of_id typ_id);
      let substs =
        List.fold_left2 (fun substs param ctyp -> KBindings.add param ctyp substs) KBindings.empty params ctyps
      in
      Bindings.map (subst_poly substs) constructors

let struct_field_bindings l ctx ctyp =
  match ctyp with
  | CT_struct (struct_id, args) ->
      let field_ctyps = instantiate_polymorphic_type ~at:l struct_id args ctx.records in
      (struct_id, field_ctyps)
  | _ -> Reporting.unreachable l __POS__ ("Expected struct ctyp, got " ^ string_of_ctyp ctyp)

let struct_fields l ctx ctyp =
  let struct_id, field_ctyps = struct_field_bindings l ctx ctyp in
  ( struct_id,
    fun id ->
      match Bindings.find_opt id field_ctyps with
      | Some ctyp -> ctyp
      | None ->
          Reporting.unreachable l __POS__ ("Failed to find field " ^ string_of_id id ^ " in " ^ string_of_ctyp ctyp)
  )

let variant_constructor_bindings l ctx ctyp =
  match ctyp with
  | CT_variant (var_id, args) ->
      let ctor_ctyps = instantiate_polymorphic_type ~at:l var_id args ctx.variants in
      (var_id, ctor_ctyps)
  | _ -> Reporting.unreachable l __POS__ ("Expected variant ctyp, got " ^ string_of_ctyp ctyp)

let enum_members l ctx id =
  match Bindings.find_opt id ctx.enums with
  | Some elems -> elems
  | None -> Reporting.unreachable l __POS__ ("Failed to find enum type " ^ string_of_id id)

let transparent_newtype ctx = function
  | CT_variant (id, args) when Env.is_newtype id ctx.tc_env ->
      instantiate_polymorphic_type ~at:(id_loc id) id args ctx.variants |> Bindings.choose |> snd
  | ctyp -> ctyp

let update_coverage_override' ctx = function
  | Some (_, Some (AD_aux (AD_string "on", _))) -> { ctx with coverage_override = true }
  | Some (_, Some (AD_aux (AD_string "off", _))) -> { ctx with coverage_override = false }
  | _ -> ctx

let update_coverage_override uannot ctx = update_coverage_override' ctx (get_attribute "coverage" uannot)

let update_coverage_override_def def_annot ctx = update_coverage_override' ctx (get_def_attribute "coverage" def_annot)

let rec mangle_string_of_ctyp ctx = function
  | CT_lint -> "i"
  | CT_fint n -> "I" ^ string_of_int n
  | CT_fuint n -> "U" ^ string_of_int n
  | CT_lbits -> "b"
  | CT_sbits n -> "S" ^ string_of_int n
  | CT_fbits n -> "B" ^ string_of_int n
  | CT_constant n -> "C" ^ Big_int.to_string n
  | CT_unit -> "u"
  | CT_bool -> "o"
  | CT_real -> "r"
  | CT_string -> "s"
  | CT_float n -> "f" ^ string_of_int n
  | CT_rounding_mode -> "m"
  | CT_json -> "j"
  | CT_json_key -> "k"
  | CT_enum id -> "E" ^ string_of_id id ^ "%"
  | CT_ref ctyp -> "&" ^ mangle_string_of_ctyp ctx ctyp
  | CT_memory_writes -> "w"
  | CT_tup ctyps -> "(" ^ Util.string_of_list "," (mangle_string_of_ctyp ctx) ctyps ^ ")"
  | CT_struct (id, ctyps) -> (
      match ctyps with
      | [] -> "R" ^ string_of_id id
      | _ -> "R" ^ string_of_id id ^ "<" ^ Util.string_of_list "," (mangle_string_of_ctyp ctx) ctyps ^ ">"
    )
  | CT_variant (id, ctyps) -> (
      let id_str = string_of_id id in
      let prefix = if id_str = "option" then "O" else "U" ^ id_str in
      match ctyps with
      | [] -> prefix
      | _ -> prefix ^ "<" ^ Util.string_of_list "," (mangle_string_of_ctyp ctx) ctyps ^ ">"
    )
  | CT_vector ctyp -> "V" ^ mangle_string_of_ctyp ctx ctyp
  | CT_fvector (n, ctyp) -> "F" ^ string_of_int n ^ mangle_string_of_ctyp ctx ctyp
  | CT_list ctyp -> "L" ^ mangle_string_of_ctyp ctx ctyp
  | CT_poly kid -> "P" ^ string_of_kid kid

module type CONFIG = sig
  val convert_typ : ctx -> typ -> ctyp
  val ctyp_suprema : ctyp -> ctyp
  val specialize_newtype_payload : id -> ctyp -> ctyp
  val specialize_struct_field : id -> id -> ctyp -> ctyp
  val specialize_declared_function_argument : id -> int -> ctyp -> ctyp
  val specialize_declared_function_result : id -> ctyp -> ctyp
  val propagate_anf_temporary_representation : semantic:ctyp -> represented:ctyp -> bool
  val representation_refines : semantic:ctyp -> represented:ctyp -> bool
  val specialize_function_argument_representation : semantic:ctyp -> represented:ctyp -> bool

  val specialize_function_result_representation : semantic:ctyp -> represented:ctyp -> bool

  val specialize_function_body_representation : semantic:ctyp -> represented:ctyp -> bool

  (** When backend specialization is enabled, an immutable top-level integer may use the exact bound inferred from its
      initializer even when [unsigned(...)] gave the binding the otherwise-unbounded semantic type [int]. *)
  val specialize_c : bool

  (** Whether the backend should reject any arbitrary-precision integers that remain after specialization. This is an
      audit only: it must not select representations or otherwise change lowering. *)
  val require_bounded_int : bool

  (** The mathematical interval represented by a concrete integer storage type. Representation specialization uses this
      to propagate call-site bounds through every value written during a local variable's lifetime. *)
  val integer_representation_bounds : ctyp -> (Big_int.num * Big_int.num) option

  val specialized_function_external : id -> ctyp list -> ctyp -> id option
  val function_argument_unification_type : expected:ctyp -> represented:ctyp -> ctyp option
  val function_argument_narrowing_allowed : expected:ctyp -> source:ctyp -> represented:ctyp -> bool
  val preserve_aval_representation : semantic:ctyp -> represented:ctyp -> bool
  val propagate_newtype_payload_representation : id -> semantic:ctyp -> represented:ctyp -> bool
  val specialize_call_result : id -> ctyp list -> ctyp -> ctyp
  val specialize_call_destination : ctx -> id -> ctyp list -> semantic:ctyp -> represented:ctyp -> bool
  val specialize_call_argument : ctx -> id -> ctyp -> ctyp list -> int -> semantic:ctyp -> represented:ctyp -> bool
  val optimize_anf : ctx -> typ aexp -> typ aexp
  val unroll_loops : int option
  val make_call_precise : ctx -> id -> ctyp list -> ctyp -> bool
  val ignore_64 : bool
  val struct_value : bool
  val tuple_value : bool
  val use_real : bool
  val branch_coverage : out_channel option
  val track_throw : bool
  val assert_to_exception : bool
  val erase_assert_messages : bool
  val use_void : bool
  val eager_control_flow : bool
  val preserve_types : IdSet.t
  val fun_to_wires : int Bindings.t
end

module IdGraph = Graph.Make (Id)
module IdGraphNS = Set.Make (Id)

let callgraph cdefs =
  List.fold_left
    (fun graph cdef ->
      match cdef with
      | CDEF_aux (CDEF_fundef (id, _, _, body), _) ->
          let graph = ref graph in
          List.iter
            (iter_instr (function
              | I_aux (I_funcall (_, _, (call, _), _), _) -> graph := IdGraph.add_edge id call !graph
              | _ -> ()
              ))
            body;
          !graph
      | _ -> graph
    )
    IdGraph.empty cdefs

module Make (C : CONFIG) = struct
  let ctyp_of_typ ctx typ = C.convert_typ ctx typ

  let generic_signature quant arg_typs ret_typ =
    let quantified =
      quant_kopts quant |> List.map kopt_kid |> List.filter (fun kid -> not (is_kid_generated kid)) |> KidSet.of_list
    in
    let dependencies typ = KidSet.inter quantified (tyvars_of_typ typ) in
    { generic_parameters = List.map dependencies arg_typs; generic_result = dependencies ret_typ }

  let position_is_generic dependencies = not (KidSet.is_empty dependencies)

  let rec chunkify n xs = match (Util.take n xs, Util.drop n xs) with xs, [] -> [xs] | xs, ys -> xs :: chunkify n ys

  (* Counters to provide unique IDs for branches, branch targets and functions. *)
  let coverage_branch_count = ref 0
  let coverage_branch_target_count = ref 0
  let coverage_function_count = ref 0

  let coverage_loc_args l =
    match Reporting.simp_loc l with
    (* Scattered definitions may not have a known location but we still want
       to measure coverage of them. *)
    | None -> "\"\", 0, 0, 0, 0"
    | Some (p1, p2) ->
        Printf.sprintf "\"%s\", %d, %d, %d, %d" (String.escaped p1.pos_fname) p1.pos_lnum (p1.pos_cnum - p1.pos_bol)
          p2.pos_lnum (p2.pos_cnum - p2.pos_bol)

  (* A branch is a `match` (including `mapping`), `if` or short-circuiting and/or.
     This returns a new ID for the branch, and the C code to call. It also
     writes the static branch info to C.branch_coverage. *)
  let coverage_branch_reached ctx l =
    match C.branch_coverage with
    | Some out when ctx.coverage_override ->
        let branch_id = !coverage_branch_count in
        incr coverage_branch_count;
        let args = coverage_loc_args l in
        Printf.fprintf out "%s\n" ("B " ^ string_of_int branch_id ^ ", " ^ args);
        (branch_id, [iraw (Printf.sprintf "sail_branch_reached(%d, %s);" branch_id args)])
    | _ -> (0, [])

  let append_into_block instrs instr = match instrs with [] -> instr | _ -> iblock (instrs @ [instr])

  let rec find_aexp_loc (AE_aux (e, { loc = l; _ })) =
    match Reporting.simp_loc l with
    | Some _ -> l
    | None -> (
        match e with AE_typ (e', _) -> find_aexp_loc e' | _ -> l
      )

  (* This is called when an *arm* of a branch is taken. For example if you
     have a `match`, it is called for the match arm that is taken.
     For `if` without `else` then it may not be called at all. Same for
     short-circuiting boolean expressions. `branch_id` is the ID for the entire
     conditional expression (the whole `match` etc.). *)
  let coverage_branch_target_taken ctx branch_id aexp =
    match C.branch_coverage with
    | Some out when ctx.coverage_override ->
        let branch_target_id = !coverage_branch_target_count in
        incr coverage_branch_target_count;
        let args = coverage_loc_args (find_aexp_loc aexp) in
        Printf.fprintf out "%s\n" ("T " ^ string_of_int branch_id ^ ", " ^ string_of_int branch_target_id ^ ", " ^ args);
        [iraw (Printf.sprintf "sail_branch_target_taken(%d, %d, %s);" branch_id branch_target_id args)]
    | _ -> []

  (* Generate code and static branch info for function entry coverage.
     `id` is the name of the function. *)
  let coverage_function_entry ctx id l =
    match C.branch_coverage with
    | Some out when ctx.coverage_override ->
        let function_id = !coverage_function_count in
        incr coverage_function_count;
        let args = coverage_loc_args l in
        Printf.fprintf out "%s\n" ("F " ^ string_of_int function_id ^ ", \"" ^ string_of_id id ^ "\", " ^ args);
        [iraw (Printf.sprintf "sail_function_entry(%d, \"%s\", %s);" function_id (string_of_id id) args)]
    | _ -> []

  let unit_cval = V_lit (VL_unit, CT_unit)

  let assert_exception l msg =
    let exception_ctyp = CT_variant (mk_id "exception", []) in
    let e = ngensym () in
    ( [idecl l exception_ctyp e; ifuncall l (CL_id (e, exception_ctyp)) (mk_id "__assertion_failed#", []) [msg]],
      V_id (e, exception_ctyp)
    )

  let get_variable_ctyp id ctx =
    match NameMap.find_opt id ctx.locals with
    | Some binding -> Some binding
    | None -> (
        match id with
        | Name (id, _) -> (
            match Bindings.find_opt id ctx.registers with
            | Some ctyp -> Some (Mutable, ctyp)
            | None -> (
                match Bindings.find_opt id ctx.letbind_ctyps with Some ctyp -> Some (Immutable, ctyp) | None -> None
              )
          )
        | _ -> None
      )

  let rec compile_aval l ctx = function
    | AV_cval (cval, typ) ->
        let ctyp = cval_ctyp cval in
        let ctyp' = ctyp_of_typ ctx typ in
        if ctyp_equal ctyp ctyp' then ([], cval, [])
        else (
          match (ctyp, ctyp') with
          | _ when C.preserve_aval_representation ~semantic:ctyp' ~represented:ctyp ->
              (* Structural POD values may stay native while ANF still carries
                 their semantic Sail annotation. Checked integer refinements
                 deliberately do not take this path. *)
              ([], cval, [])
          | _ ->
              let gs = ngensym () in
              ([iinit l ctyp' gs cval], V_id (gs, ctyp'), [iclear ctyp' gs])
        )
    | AV_id (Name (id, _), Enum typ) -> ([], V_member (id, ctyp_of_typ ctx typ), [])
    | AV_id (id, typ) -> (
        match get_variable_ctyp id ctx with
        | Some (_, ctyp) -> ([], V_id (id, ctyp), [])
        | None -> ([], V_id (id, ctyp_of_typ ctx (lvar_typ typ)), [])
      )
    | AV_abstract (id, typ) -> (
        match Bindings.find_opt id ctx.abstracts with
        | Some (ctyp, _) -> ([], V_id (Abstract id, ctyp), [])
        | None ->
            Reporting.unreachable l __POS__ ("Failed to find a C-type for abstract type variable " ^ string_of_id id)
      )
    | AV_ref (id, typ) -> ([], V_lit (VL_ref (string_of_id id), CT_ref (ctyp_of_typ ctx (lvar_typ typ))), [])
    | AV_lit (L_aux (L_string str, _), typ) -> ([], V_lit (VL_string (String.escaped str), ctyp_of_typ ctx typ), [])
    | AV_lit (L_aux (L_num n, _), typ) ->
        let ctyp = ctyp_of_typ ctx typ in
        if C.ignore_64 then ([], V_lit (VL_int n, ctyp), [])
        else (
          match C.integer_representation_bounds ctyp with
          | Some (lower, upper) when Big_int.less_equal lower n && Big_int.less_equal n upper ->
              (* Preserve any fixed representation already selected for a
                 bounded literal, including unsigned values above INT64_MAX
                 and custom wide integers.  Falling through to the managed
                 string conversion here would require a nonexistent
                 string-to-native conversion and discard the proven bound. *)
              ([], V_lit (VL_int n, ctyp), [])
          | _ when Big_int.less_equal (min_int 64) n && Big_int.less_equal n (max_int 64) ->
              let gs = ngensym () in
              ([iinit l CT_lint gs (V_lit (VL_int n, CT_fint 64))], V_id (gs, CT_lint), [iclear CT_lint gs])
          | _ ->
              let gs = ngensym () in
              ( [iinit l CT_lint gs (V_lit (VL_string (Big_int.to_string n), CT_string))],
                V_id (gs, CT_lint),
                [iclear CT_lint gs]
              )
        )
    | AV_lit (L_aux (((L_hex _ | L_bin _) as l_aux), _), _) ->
        let bitlist =
          ( match l_aux with
            | L_hex hex -> BitList.of_hex_lit hex
            | L_bin bin -> BitList.of_bin_lit bin
            | _ -> assert false
            )
          |> List.map (function B0 -> Sail2_values.B0 | B1 -> Sail2_values.B1)
        in
        let len = List.length bitlist in
        (* For small bitvectors, or when we permit arbitrary-length literals > 64 we can emit a literal directly,
           otherwise we use the special append_64 builtin to construct a literal from 64-bit chunks. *)
        if len <= 64 || C.ignore_64 then ([], V_lit (VL_bits bitlist, CT_fbits len), [])
        else (
          let bv_literal len bits = V_lit (VL_bits bits, CT_fbits len) in
          let first_chunk = Util.take (len mod 64) bitlist |> bv_literal (len mod 64) in
          let chunks = Util.drop (len mod 64) bitlist |> chunkify 64 |> List.map (bv_literal 64) in
          let gs = ngensym () in
          ( [iinit l CT_lbits gs first_chunk]
            @ List.map
                (fun chunk -> ifuncall l (CL_id (gs, CT_lbits)) (mk_id "append_64", []) [V_id (gs, CT_lbits); chunk])
                chunks,
            V_id (gs, CT_lbits),
            [iclear CT_lbits gs]
          )
        )
    | AV_lit (L_aux (L_true, _), _) -> ([], V_lit (VL_bool true, CT_bool), [])
    | AV_lit (L_aux (L_false, _), _) -> ([], V_lit (VL_bool false, CT_bool), [])
    | AV_lit (L_aux (L_real r, _), _) ->
        let str = Q.to_string (Util.Rational.from_rocq r) in
        if C.use_real then ([], V_lit (VL_real str, CT_real), [])
        else (
          let gs = ngensym () in
          ([iinit l CT_real gs (V_lit (VL_string str, CT_string))], V_id (gs, CT_real), [iclear CT_real gs])
        )
    | AV_lit (L_aux (L_unit, _), _) -> ([], V_lit (VL_unit, CT_unit), [])
    | AV_undef typ ->
        let ctyp = ctyp_of_typ ctx typ in
        ([], V_lit (VL_undefined, ctyp), [])
    | AV_tuple avals ->
        let elements = List.map (compile_aval l ctx) avals in
        let cvals = List.map (fun (_, cval, _) -> cval) elements in
        let setup = List.concat (List.map (fun (setup, _, _) -> setup) elements) in
        let cleanup = List.concat (List.rev (List.map (fun (_, _, cleanup) -> cleanup) elements)) in
        let tup_ctyp = CT_tup (List.map cval_ctyp cvals) in
        let gs = ngensym () in
        if C.tuple_value then (setup, V_tuple cvals, cleanup)
        else
          ( setup
            @ [idecl l tup_ctyp gs]
            @ List.mapi (fun n cval -> icopy l (CL_tuple (CL_id (gs, tup_ctyp), n)) cval) cvals,
            V_id (gs, CT_tup (List.map cval_ctyp cvals)),
            [iclear tup_ctyp gs] @ cleanup
          )
    | AV_record (fields, typ) when C.struct_value ->
        let ctyp = ctyp_of_typ ctx typ in
        let compile_fields (id, aval) =
          let field_setup, cval, field_cleanup = compile_aval l ctx aval in
          (field_setup, (id, cval), field_cleanup)
        in
        let field_triples = List.map compile_fields (Bindings.bindings fields) in
        let setup = List.concat (List.map (fun (s, _, _) -> s) field_triples) in
        let fields = List.map (fun (_, f, _) -> f) field_triples in
        let cleanup = List.concat (List.map (fun (_, _, c) -> c) field_triples) in
        (setup, V_struct (fields, ctyp), cleanup)
    | AV_record (fields, typ) ->
        let ctyp = ctyp_of_typ ctx typ in
        let _, field_ctyp = struct_fields l ctx ctyp in
        let gs = ngensym () in
        let compile_fields (id, aval) =
          let field_setup, cval, field_cleanup = compile_aval l ctx aval in
          field_setup @ [icopy l (CL_field (CL_id (gs, ctyp), id, field_ctyp id)) cval] @ field_cleanup
        in
        ( [idecl l ctyp gs] @ List.concat (List.map compile_fields (Bindings.bindings fields)),
          V_id (gs, ctyp),
          [iclear ctyp gs]
        )
    | AV_vector ([], typ) -> (
        let vector_ctyp = ctyp_of_typ ctx typ in
        match ctyp_of_typ ctx typ with
        | CT_fbits 0 -> ([], V_lit (VL_bits [], vector_ctyp), [])
        | _ ->
            let gs = ngensym () in
            ( [
                idecl l vector_ctyp gs;
                iextern l
                  (CL_id (gs, vector_ctyp))
                  (mk_id "internal_vector_init", [])
                  [V_lit (VL_int Big_int.zero, CT_fint 64)];
              ],
              V_id (gs, vector_ctyp),
              [iclear vector_ctyp gs]
            )
      )
    (* If we have a bitvector value, that isn't a literal then we need to set bits individually. *)
    | AV_vector (avals, Typ_aux (Typ_app (id, _), _)) when string_of_id id = "bitvector" && List.length avals <= 64 ->
        let len = List.length avals in
        let gs = ngensym () in
        let ctyp = CT_fbits len in
        let mask i =
          VL_bits
            (Util.list_init (63 - i) (fun _ -> Sail2_values.B0)
            @ [Sail2_values.B1]
            @ Util.list_init i (fun _ -> Sail2_values.B0)
            )
        in
        let aval_mask i aval =
          let setup, cval, cleanup = compile_aval l ctx aval in
          match cval with
          | V_lit (VL_bits [Sail2_values.B0], _) -> []
          | V_lit (VL_bits [Sail2_values.B1], _) ->
              [icopy l (CL_id (gs, ctyp)) (V_call (Bvor, [V_id (gs, ctyp); V_lit (mask i, ctyp)]))]
          | _ ->
              setup
              @ [
                  iextern l
                    (CL_id (gs, ctyp))
                    (mk_id "update_fbits", [])
                    [V_id (gs, ctyp); V_lit (VL_int (Big_int.of_int i), CT_constant (Big_int.of_int i)); cval];
                ]
              @ cleanup
        in
        ( [
            idecl l ctyp gs;
            icopy l (CL_id (gs, ctyp)) (V_lit (VL_bits (Util.list_init len (fun _ -> Sail2_values.B0)), ctyp));
          ]
          @ List.concat (List.mapi aval_mask (List.rev avals)),
          V_id (gs, ctyp),
          []
        )
    (* Compiling a vector literal that isn't a bitvector *)
    | AV_vector (avals, Typ_aux (Typ_app (id, [_; A_aux (A_typ typ, _)]), _)) when string_of_id id = "vector" ->
        let ord = Env.get_default_order ctx.tc_env in
        let len = List.length avals in
        let direction = match ord with Ord_aux (Ord_inc, _) -> false | Ord_aux (Ord_dec, _) -> true in
        let elem_ctyp = ctyp_of_typ ctx typ in
        let vector_ctyp = CT_fvector (len, elem_ctyp) in
        let gs = ngensym () in
        let aval_set i aval =
          let setup, cval, cleanup = compile_aval l ctx aval in
          let cval, conversion_setup, conversion_cleanup =
            if ctyp_equal (cval_ctyp cval) elem_ctyp then (cval, [], [])
            else (
              let gs = ngensym () in
              (V_id (gs, elem_ctyp), [iinit l elem_ctyp gs cval], [iclear elem_ctyp gs])
            )
          in
          setup @ conversion_setup
          @ [
              iextern l
                (CL_id (gs, vector_ctyp))
                (mk_id "internal_vector_update", [])
                [V_id (gs, vector_ctyp); V_lit (VL_int (Big_int.of_int i), CT_fint 64); cval];
            ]
          @ conversion_cleanup @ cleanup
        in
        ( [
            idecl l vector_ctyp gs;
            iextern l
              (CL_id (gs, vector_ctyp))
              (mk_id "internal_vector_init", [])
              [V_lit (VL_int (Big_int.of_int len), CT_fint 64)];
          ]
          @ List.concat (List.mapi aval_set (if direction then List.rev avals else avals)),
          V_id (gs, vector_ctyp),
          [iclear vector_ctyp gs]
        )
    | AV_vector _ as aval ->
        raise
          (Reporting.err_general l
             ("Have AVL_vector: " ^ Document.to_string (pp_aval aval) ^ " which is not a vector type")
          )
    | AV_list (avals, Typ_aux (typ, _)) ->
        let ctyp =
          match typ with
          | Typ_app (id, [A_aux (A_typ typ, _)]) when string_of_id id = "list" -> C.ctyp_suprema (ctyp_of_typ ctx typ)
          | _ -> raise (Reporting.err_general l "Invalid list type")
        in
        let gs = ngensym () in
        let mk_cons aval =
          let setup, cval, cleanup = compile_aval l ctx aval in
          setup
          @ [iextern l (CL_id (gs, CT_list ctyp)) (mk_id "sail_cons", [ctyp]) [cval; V_id (gs, CT_list ctyp)]]
          @ cleanup
        in
        ( [idecl l (CT_list ctyp) gs] @ List.concat (List.map mk_cons (List.rev avals)),
          V_id (gs, CT_list ctyp),
          [iclear (CT_list ctyp) gs]
        )

  (** Compile a function call.

      If called as [compile_funcall ~override_id:foo l ctx bar args], then we will compile as if we are calling [bar],
      but insert a call to [foo] in the IR. This is used for optimizations where we can generate a more efficient
      version of [foo] that doesn't exist in the original Sail. *)
  type partial_integer_interval = Big_int.num option * Big_int.num option

  let tighter_integer_interval (left_lower, left_upper) (right_lower, right_upper) =
    let tighter_lower =
      match (left_lower, right_lower) with
      | Some left, Some right -> Some (Big_int.max left right)
      | Some bound, None | None, Some bound -> Some bound
      | None, None -> None
    in
    let tighter_upper =
      match (left_upper, right_upper) with
      | Some left, Some right -> Some (Big_int.min left right)
      | Some bound, None | None, Some bound -> Some bound
      | None, None -> None
    in
    (tighter_lower, tighter_upper)

  let wider_integer_interval (left_lower, left_upper) (right_lower, right_upper) =
    let wider_lower =
      match (left_lower, right_lower) with Some left, Some right -> Some (Big_int.min left right) | _ -> None
    in
    let wider_upper =
      match (left_upper, right_upper) with Some left, Some right -> Some (Big_int.max left right) | _ -> None
    in
    (wider_lower, wider_upper)

  let direct_integer_interval nexp constraints =
    let constant = function Nexp_aux (Nexp_constant value, _) -> Some value | _ -> None in
    let nexp_is_target candidate = nexp_identical (nexp_simp candidate) nexp in
    let rec constraint_interval (NC_aux (constraint_aux, _)) =
      match constraint_aux with
      | NC_equal (A_aux (A_nexp left, _), A_aux (A_nexp right, _)) -> (
          match (nexp_is_target left, constant right, nexp_is_target right, constant left) with
          | true, Some value, _, _ | _, _, true, Some value -> (Some value, Some value)
          | _ -> (None, None)
        )
      | NC_ge (left, right) -> (
          match (nexp_is_target left, constant right, nexp_is_target right, constant left) with
          | true, Some value, _, _ -> (Some value, None)
          | _, _, true, Some value -> (None, Some value)
          | _ -> (None, None)
        )
      | NC_gt (left, right) -> (
          match (nexp_is_target left, constant right, nexp_is_target right, constant left) with
          | true, Some value, _, _ -> (Some (Big_int.succ value), None)
          | _, _, true, Some value -> (None, Some (Big_int.pred value))
          | _ -> (None, None)
        )
      | NC_le (left, right) -> (
          match (nexp_is_target left, constant right, nexp_is_target right, constant left) with
          | true, Some value, _, _ -> (None, Some value)
          | _, _, true, Some value -> (Some value, None)
          | _ -> (None, None)
        )
      | NC_lt (left, right) -> (
          match (nexp_is_target left, constant right, nexp_is_target right, constant left) with
          | true, Some value, _, _ -> (None, Some (Big_int.pred value))
          | _, _, true, Some value -> (Some (Big_int.succ value), None)
          | _ -> (None, None)
        )
      | NC_set (candidate, values) when nexp_is_target candidate && values <> [] ->
          ( Some (List.fold_left Big_int.min (List.hd values) (List.tl values)),
            Some (List.fold_left Big_int.max (List.hd values) (List.tl values))
          )
      | NC_and (left, right) -> tighter_integer_interval (constraint_interval left) (constraint_interval right)
      | NC_or (left, right) -> wider_integer_interval (constraint_interval left) (constraint_interval right)
      | _ -> (None, None)
    in
    List.fold_left
      (fun interval nc -> tighter_integer_interval interval (constraint_interval nc))
      (None, None) constraints

  let source_integer_interval env typ =
    match destruct_range env typ with
    | Some (kids, constr, lower, upper) ->
        let env = add_existential Parse_ast.Unknown (List.map (mk_kopt K_int) kids) constr env in
        let lower = nexp_simp lower in
        let upper = nexp_simp upper in
        let lower_bound =
          match solve_unique env lower with
          | Some lower -> Some lower
          | None -> fst (direct_integer_interval lower (Env.get_constraints env))
        in
        let upper_bound =
          match solve_unique env upper with
          | Some upper -> Some upper
          | None -> snd (direct_integer_interval upper (Env.get_constraints env))
        in
        Option.bind lower_bound (fun lower -> Option.map (fun upper -> (lower, upper)) upper_bound)
    | None -> (
        match destruct_bitvector env typ with
        | Some width ->
            Option.bind
              (solve_unique env (nexp_simp width))
              (fun width ->
                if Big_int.less width Big_int.zero || Big_int.greater width (Big_int.of_int Stdlib.max_int) then None
                else Jib_semantics.fixed_unsigned_bounds (Big_int.to_int width)
              )
        | None -> None
      )

  let prove_exact_arithmetic_bounds ~env ~operands ~result_typ ~result_interval ~represented =
    match C.integer_representation_bounds represented with
    | Some (lower, upper) ->
        let argument_bounds =
          List.mapi
            (fun index (typ, interval) -> Jib_semantics.prove_argument_bounds ~env ~index ~typ ~interval ~lower ~upper)
            operands
        in
        let result_bounds = Jib_semantics.prove_result_bounds ~env ~result_typ ~result_interval ~lower ~upper in
        List.filter_map Fun.id (result_bounds :: argument_bounds)
    | None -> []

  let integer_primitive_name ctx id =
    let name =
      match Bindings.find_opt id ctx.valspecs with
      | Some (Some external_name, _, _, _) -> external_name
      | _ -> string_of_id id
    in
    match name with
    | "add_int" | "add_atom" | "__sail_proven_native_add" -> Some `Add
    | "sub_int" | "sub_atom" | "__sail_proven_native_sub" -> Some `Sub
    | "mult_int" | "mult_atom" | "__sail_proven_native_mul" -> Some `Mul
    | "tdiv_int" | "tdiv_nat" | "__sail_proven_native_div" -> Some `Div
    | "tmod_int" | "tmod_nat" | "__sail_proven_native_mod" -> Some `Mod
    | "ediv_int" -> Some `Ediv
    | "emod_int" -> Some `Emod
    | _ -> None

  let compile_funcall_with ?override_id l ctx id compile_arg semantic_ctyp_of_arg semantic_typ_of_arg
      semantic_interval_of_arg args =
    let setup = ref [] in
    let cleanup = ref [] in

    let quant, Typ_aux (fn_typ, _) =
      (* If we can't find a function in local_env, fall back to the
         global env - this happens when representing assertions, exit,
         etc as functions in the IR. *)
      try Env.get_val_spec id ctx.local_env with Type_error.Type_error _ -> Env.get_val_spec id ctx.tc_env
    in
    let source_quant, Typ_aux (source_fn_typ, _) =
      (* [get_val_spec] freshens a callee's quantified variables against the
         caller environment.  Those freshened names contain [#], just like
         genuinely compiler-generated singleton variables, so they cannot be
         used to decide whether the source signature authorizes representation
         specialization.  Read the un-freshened binding solely for that
         provenance decision; keep the freshened binding above for ordinary
         call typing and unification. *)
      try Env.get_val_spec_orig id ctx.local_env with Type_error.Type_error _ -> Env.get_val_spec_orig id ctx.tc_env
    in
    let params = quant_kopts quant |> List.filter is_typ_kopt |> List.map kopt_kid in

    let arg_typs, ret_typ = match fn_typ with Typ_fn (arg_typs, ret_typ) -> (arg_typs, ret_typ) | _ -> assert false in
    let source_arg_typs, source_ret_typ =
      match source_fn_typ with Typ_fn (arg_typs, ret_typ) -> (arg_typs, ret_typ) | _ -> assert false
    in
    let generic_signature = generic_signature source_quant source_arg_typs source_ret_typ in
    let ctx' = { ctx with local_env = Env.add_typquant (id_loc id) quant ctx.local_env } in
    let arg_ctyps, ret_ctyp = (List.map (ctyp_of_typ ctx') arg_typs, ctyp_of_typ ctx' ret_typ) in

    assert (List.length arg_ctyps = List.length args);

    let instantiation = ref KBindings.empty in

    let merge_call_unifiers kid ctyp1 ctyp2 =
      (* Polymorphic calls can observe both the semantic instantiation and a
         narrower backend representation of that same type.  Keep the
         semantic type as the polymorphic instantiation; the represented
         argument remains narrow and is handled by the representation
         specialization pass. *)
      if C.specialize_function_argument_representation ~semantic:ctyp1 ~represented:ctyp2 then Some ctyp1
      else if C.specialize_function_argument_representation ~semantic:ctyp2 ~represented:ctyp1 then Some ctyp2
      else merge_unifiers kid ctyp1 ctyp2
    in

    let setup_arg _index ctyp _generic_dependencies arg =
      let arg_setup, cval, arg_cleanup = compile_arg arg in
      let represented = cval_ctyp cval in
      let semantic = semantic_ctyp_of_arg arg in
      let unification_ctyp =
        (* Compare function parameters through the backend's semantic view of
           compatible representations.  The actual argument keeps
           [represented]; call specialization or [make_calls_precise] handles
           the representation boundary after unification. *)
        if ctyp_equal ctyp semantic then ctyp
        else (
          match C.function_argument_unification_type ~expected:ctyp ~represented with
          | Some semantic_representation -> semantic_representation
          | None ->
              if
                C.representation_refines ~semantic:ctyp ~represented
                || C.function_argument_narrowing_allowed ~expected:ctyp ~source:semantic ~represented
              then ctyp
              else if C.representation_refines ~semantic ~represented then semantic
              else represented
        )
      in
      instantiation := KBindings.union merge_call_unifiers (ctyp_unify l ctyp unification_ctyp) !instantiation;
      setup := List.rev arg_setup @ !setup;
      cleanup := arg_cleanup @ !cleanup;
      cval
    in

    let setup_args =
      List.mapi
        (fun index (ctyp, (generic_dependencies, arg)) -> setup_arg index ctyp generic_dependencies arg)
        (List.combine arg_ctyps (List.combine generic_signature.generic_parameters args))
    in
    let argument_intervals = List.map semantic_interval_of_arg args in
    let result_interval = source_integer_interval ctx'.local_env ret_typ in
    let semantic_proofs =
      match (integer_primitive_name ctx id, args, argument_intervals) with
      | (Some (`Add | `Sub | `Mul) as operation), [left; right], [left_interval; right_interval] ->
          let exact_bounds =
            match (semantic_typ_of_arg left, semantic_typ_of_arg right) with
            | Some left_typ, Some right_typ ->
                prove_exact_arithmetic_bounds ~env:ctx.local_env
                  ~operands:[(left_typ, left_interval); (right_typ, right_interval)]
                  ~result_typ:ret_typ ~result_interval ~represented:ret_ctyp
            | _ -> []
          in
          let argument_order =
            match (operation, semantic_typ_of_arg left, semantic_typ_of_arg right) with
            | Some `Sub, Some left_typ, Some right_typ ->
                Jib_semantics.prove_argument_le ~env:ctx.local_env ~left_index:1 ~left_typ:right_typ
                  ~left_interval:right_interval ~right_index:0 ~right_typ:left_typ ~right_interval:left_interval
            | _ -> None
          in
          let result_nonnegative =
            match operation with
            | Some `Sub ->
                Jib_semantics.prove_result_nonnegative ~env:ctx.local_env ~result_typ:ret_typ ~result_interval
            | _ -> None
          in
          List.filter_map Fun.id [argument_order; result_nonnegative] @ exact_bounds
      | _ -> []
    in
    let call_id = Option.value ~default:id override_id in

    ( List.rev !setup,
      (fun clexp ->
        let represented = clexp_ctyp clexp in
        let semantic = subst_poly !instantiation ret_ctyp in
        let instantiation =
          if
            C.representation_refines ~semantic ~represented
            || C.representation_refines ~semantic:represented ~represented:semantic
          then !instantiation
          else KBindings.union merge_call_unifiers (ctyp_unify l ret_ctyp represented) !instantiation
        in
        let ctyp_args = List.map (fun v -> KBindings.find v instantiation) params in
        ifuncall_with_bounds ~semantic_proofs l (argument_intervals, result_interval) clexp (call_id, ctyp_args)
          setup_args
      )
      (* iblock1 (optimize_call l ctx clexp (id, KBindings.bindings unifiers |> List.map snd) setup_args arg_ctyps ret_ctyp) *),
      !cleanup
    )

  let compile_funcall ?override_id l ctx id args =
    compile_funcall_with ?override_id l ctx id (compile_aval l ctx)
      (fun arg -> ctyp_of_typ ctx (aval_typ arg))
      (fun arg -> Some (aval_typ arg))
      (fun arg -> source_integer_interval ctx.local_env (aval_typ arg))
      args

  let compile_extern l ctx id args source_return_typ return_ctyp =
    let setup = ref [] in
    let cleanup = ref [] in

    let setup_arg aval =
      let arg_setup, cval, arg_cleanup = compile_aval l ctx aval in
      setup := List.rev arg_setup @ !setup;
      cleanup := arg_cleanup @ !cleanup;
      cval
    in

    let setup_args = List.map setup_arg args in
    let argument_intervals = List.map (fun arg -> source_integer_interval ctx.local_env (aval_typ arg)) args in
    let result_interval = source_integer_interval ctx.local_env source_return_typ in

    let proven_native_op =
      match string_of_id id with
      | "__sail_proven_native_add" -> Some Proven_iadd
      | "__sail_proven_native_sub" -> Some Proven_isub
      | "__sail_proven_native_mul" -> Some Proven_imul
      | "__sail_proven_native_div" -> Some Proven_idiv
      | "__sail_proven_native_mod" -> Some Proven_imod
      | _ -> None
    in
    let source_semantic_proofs =
      match (proven_native_op, args, argument_intervals) with
      | (Some (Proven_iadd | Proven_isub | Proven_imul) as operation), [left; right], [left_interval; right_interval] ->
          let exact_bounds =
            match return_ctyp with
            | Some represented ->
                prove_exact_arithmetic_bounds ~env:ctx.local_env
                  ~operands:[(aval_typ left, left_interval); (aval_typ right, right_interval)]
                  ~result_typ:source_return_typ ~result_interval ~represented
            | None -> []
          in
          let argument_order =
            match operation with
            | Some Proven_isub ->
                Jib_semantics.prove_argument_le ~env:ctx.local_env ~left_index:1 ~left_typ:(aval_typ right)
                  ~left_interval:right_interval ~right_index:0 ~right_typ:(aval_typ left) ~right_interval:left_interval
            | _ -> None
          in
          let result_nonnegative =
            match operation with
            | Some Proven_isub ->
                Jib_semantics.prove_result_nonnegative ~env:ctx.local_env ~result_typ:source_return_typ ~result_interval
            | _ -> None
          in
          List.filter_map Fun.id [argument_order; result_nonnegative] @ exact_bounds
      | _ -> []
    in
    let compile_call clexp =
      let operation_representation =
        match (clexp_ctyp clexp, return_ctyp) with
        | represented, _ when Option.is_some (C.integer_representation_bounds represented) -> Some represented
        | _, Some represented when Option.is_some (C.integer_representation_bounds represented) -> Some represented
        | _ -> None
      in
      let semantic_proofs =
        match (proven_native_op, operation_representation, args, argument_intervals) with
        | Some (Proven_idiv | Proven_imod), Some represented, [left; right], [left_interval; right_interval] ->
            let argument_bounds =
              prove_exact_arithmetic_bounds ~env:ctx.local_env
                ~operands:[(aval_typ left, left_interval); (aval_typ right, right_interval)]
                ~result_typ:source_return_typ ~result_interval ~represented
            in
            let excludes index arg interval value =
              Jib_semantics.prove_argument_excludes ~env:ctx.local_env ~index ~typ:(aval_typ arg) ~interval ~value
            in
            let divisor_nonzero = excludes 1 right right_interval Big_int.zero in
            let signed_overflow_exclusion =
              match represented with
              | CT_fint width -> (
                  match excludes 0 left left_interval (min_int width) with
                  | Some proof -> Some proof
                  | None -> excludes 1 right right_interval (Big_int.of_int (-1))
                )
              | _ -> None
            in
            argument_bounds @ List.filter_map Fun.id [divisor_nonzero; signed_overflow_exclusion]
        | _ -> source_semantic_proofs
      in
      if !opt_debug_function_representations && Option.is_some proven_native_op then (
        let string_of_interval = function
          | Some (lower, upper) -> Big_int.to_string lower ^ ".." ^ Big_int.to_string upper
          | None -> "?"
        in
        Printf.eprintf
          "C semantic proof: primitive=%s args=[%s] intervals=[%s] source-result=%s return=%s destination=%s \
           operation=%s proofs=%d\n\
           %!"
          (string_of_id id)
          (Util.string_of_list "," (fun arg -> string_of_typ (aval_typ arg)) args)
          (Util.string_of_list "," string_of_interval argument_intervals)
          (string_of_interval result_interval)
          (match return_ctyp with Some ctyp -> string_of_ctyp ctyp | None -> "?")
          (string_of_ctyp (clexp_ctyp clexp))
          (match operation_representation with Some ctyp -> string_of_ctyp ctyp | None -> "?")
          (List.length semantic_proofs)
      );
      match (proven_native_op, operation_representation, setup_args, semantic_proofs) with
      | Some _, Some represented, _, _ :: _ ->
          (* Keep the call boundary until the semantic-web pass has consumed
             its source proof.  Ordinary primitive specialization lowers it
             to the same native [V_call] if no larger transformation applies. *)
          if ctyp_equal (clexp_ctyp clexp) represented then
            ifuncall_with_bounds ~semantic_proofs l (argument_intervals, result_interval) clexp (id, []) setup_args
          else (
            let temporary = ngensym ~source_name:"integer_result" ~source_type:(string_of_ctyp represented) () in
            iblock
              [
                idecl l represented temporary;
                ifuncall_with_bounds ~semantic_proofs l (argument_intervals, result_interval)
                  (CL_id (temporary, represented))
                  (id, []) setup_args;
                icopy l clexp (V_id (temporary, represented));
                iclear ~loc:l represented temporary;
              ]
          )
      | _, _, _, _ :: _ ->
          ifuncall_with_bounds ~semantic_proofs l (argument_intervals, result_interval) clexp (id, []) setup_args
      | Some ((Proven_iadd | Proven_isub | Proven_imul) as op), Some represented, [left; right], [] ->
          (* The ANF optimizer emits this marker only after proving that both
             operands and the result fit [represented].  Promote before the
             operation so mixed-width arithmetic has the selected lifetime
             representation at the operation itself: assigning the result of
             uint64_t subtraction to __int128 afterwards would be too late. *)
          let promote cval =
            if ctyp_equal (cval_ctyp cval) represented then ([], cval, [])
            else (
              let promoted = ngensym ~source_name:"integer_operand" ~source_type:(string_of_ctyp represented) () in
              ( [idecl l represented promoted; icopy l (CL_id (promoted, represented)) cval],
                V_id (promoted, represented),
                [iclear represented promoted]
              )
            )
          in
          let left_setup, left, left_cleanup = promote left in
          let right_setup, right, right_cleanup = promote right in
          let operation = V_call (op, [left; right]) in
          let operation_instrs =
            if ctyp_equal (clexp_ctyp clexp) represented then [icopy l clexp operation]
            else (
              let result = ngensym ~source_name:"integer_result" ~source_type:(string_of_ctyp represented) () in
              [
                idecl l represented result;
                icopy l (CL_id (result, represented)) operation;
                icopy l clexp (V_id (result, represented));
                iclear represented result;
              ]
            )
          in
          iblock (left_setup @ right_setup @ operation_instrs @ right_cleanup @ left_cleanup)
      | Some (Proven_idiv | Proven_imod), _, _, [] ->
          (* A marker without explicit definedness evidence is not authority
             to emit C division. This defensive fallback also prevents a
             future producer from accidentally treating the marker name
             itself as proof. Keep it until the late resolver, which can
             restore the managed operand boundary if no proof emerges from
             graph specialization. *)
          ifuncall_with_bounds l (argument_intervals, result_interval) clexp (id, []) setup_args
      | _, _, _, [] -> iextern ?return_ctyp l clexp (id, []) setup_args
    in
    (List.rev !setup, compile_call, !cleanup)

  let select_abstract l ctx string_id f =
    let rec if_chain = function [] -> [] | [(_, e)] -> e | (i, t) :: e -> [iif l i t (if_chain e)] in
    Bindings.bindings ctx.abstracts
    |> List.map (fun (id, ctyp) ->
        (V_call (String_eq, [V_id (string_id, CT_string); V_lit (VL_string (string_of_id id), CT_string)]), f id ctyp)
    )
    |> if_chain

  let static_load l ctyp f =
    let loaded, loaded_instr = istatic l CT_bool (VL_bool false) in
    let s, s_instr = istatic l ctyp VL_undefined in
    ( [
        loaded_instr;
        s_instr;
        iif l
          (V_call (Bnot, [V_id (loaded, CT_bool)]))
          (f s @ [icopy l (CL_id (loaded, CT_bool)) (V_lit (VL_bool true, CT_bool))])
          [];
      ],
      (fun clexp -> icopy l clexp (V_id (s, ctyp))),
      []
    )

  let compile_config' l ctx key ctyp =
    let key_name = ngensym () in
    let json = ngensym () in
    let args = [V_lit (VL_int (Big_int.of_int (List.length key)), CT_fint 64); V_id (key_name, CT_json_key)] in
    let init =
      [
        ijson_key l key_name key;
        idecl l CT_json json;
        iextern l (CL_id (json, CT_json)) (mk_id "sail_config_get", []) args;
      ]
    in

    let config_extract ctyp json ~validate ~extract =
      let valid = ngensym () in
      let value = ngensym () in
      ( [
          idecl l CT_bool valid;
          iextern l (CL_id (valid, CT_bool)) (mk_id (fst validate), []) ([V_id (json, CT_json)] @ snd validate);
          iif l (V_call (Bnot, [V_id (valid, CT_bool)])) [ibad_config l] [];
          idecl l ctyp value;
          iextern l (CL_id (value, ctyp)) (mk_id extract, []) [V_id (json, CT_json)];
        ],
        (fun clexp -> icopy l clexp (V_id (value, ctyp))),
        [iclear ctyp value]
      )
    in

    let config_extract_bits ctyp json =
      let value = ngensym () in
      let is_abstract = ngensym () in
      let abstract_name = ngensym () in
      let setup, non_abstract_call, cleanup =
        config_extract ctyp json ~validate:("sail_config_is_bits", []) ~extract:"sail_config_unwrap_bits"
      in
      ( [
          idecl l CT_bool is_abstract;
          iextern l (CL_id (is_abstract, CT_bool)) (mk_id "sail_config_is_bits_abstract", []) [V_id (json, CT_json)];
          idecl l ctyp value;
          iif l
            (V_id (is_abstract, CT_bool))
            ([
               idecl l CT_string abstract_name;
               iextern l
                 (CL_id (abstract_name, CT_string))
                 (mk_id "sail_config_bits_abstract_len", [])
                 [V_id (json, CT_json)];
             ]
            @ select_abstract l ctx abstract_name (fun id (abstract_ctyp, _) ->
                match abstract_ctyp with
                | CT_fint 64 ->
                    [
                      iextern l
                        (CL_id (value, ctyp))
                        (mk_id "sail_config_unwrap_abstract_bits", [])
                        [V_id (Abstract id, abstract_ctyp); V_id (json, CT_json)];
                    ]
                | CT_lint | CT_fint _ | CT_fuint _ ->
                    let len = ngensym () in
                    [
                      iinit l (CT_fint 64) len (V_id (Abstract id, abstract_ctyp));
                      iextern l
                        (CL_id (value, ctyp))
                        (mk_id "sail_config_unwrap_abstract_bits", [])
                        [V_id (len, CT_fint 64); V_id (json, CT_json)];
                    ]
                | _ -> []
            )
            @ [iclear CT_string abstract_name]
            )
            (setup @ [non_abstract_call (CL_id (value, ctyp))] @ cleanup);
        ],
        (fun clexp -> icopy l clexp (V_id (value, ctyp))),
        [iclear ctyp value]
      )
    in

    let rec extract json = function
      | CT_string ->
          config_extract CT_string json ~validate:("sail_config_is_string", []) ~extract:"sail_config_unwrap_string"
      | CT_unit -> ([], (fun clexp -> icopy l clexp unit_cval), [])
      | CT_lint -> config_extract CT_lint json ~validate:("sail_config_is_int", []) ~extract:"sail_config_unwrap_int"
      | CT_fint _ -> config_extract CT_lint json ~validate:("sail_config_is_int", []) ~extract:"sail_config_unwrap_int"
      | CT_fuint _ -> config_extract CT_lint json ~validate:("sail_config_is_int", []) ~extract:"sail_config_unwrap_int"
      | CT_lbits -> config_extract_bits CT_lbits json
      | CT_sbits _ -> config_extract_bits CT_lbits json
      | CT_fbits _ -> config_extract_bits CT_lbits json
      | CT_bool -> config_extract CT_bool json ~validate:("sail_config_is_bool", []) ~extract:"sail_config_unwrap_bool"
      | CT_enum enum_id as enum_ctyp ->
          assert (Bindings.mem enum_id ctx.enums);
          let members = Bindings.find enum_id ctx.enums |> IdSet.elements in
          let enum_name = ngensym () in
          let enum_str = ngensym () in
          let setup, get_string, cleanup =
            config_extract CT_string json ~validate:("sail_config_is_string", []) ~extract:"sail_config_unwrap_string"
          in
          let enum_compare =
            List.fold_left
              (fun rest m ->
                [
                  iif l
                    (V_call (String_eq, [V_id (enum_str, CT_string); V_lit (VL_string (string_of_id m), CT_string)]))
                    [icopy l (CL_id (enum_name, enum_ctyp)) (V_member (m, enum_ctyp))]
                    rest;
                ]
              )
              [ibad_config l]
              members
          in
          ( [idecl l enum_ctyp enum_name; idecl l CT_string enum_str]
            @ setup
            @ [get_string (CL_id (enum_str, CT_string))]
            @ enum_compare,
            (fun clexp -> icopy l clexp (V_id (enum_name, enum_ctyp))),
            cleanup @ [iclear CT_string enum_str; iclear enum_ctyp enum_name]
          )
      | CT_variant (variant_id, args) as variant_ctyp ->
          let constructors = instantiate_polymorphic_type ~at:l variant_id args ctx.variants |> Bindings.bindings in
          let variant_name = ngensym () in
          let ctor_checks, ctor_extracts =
            Util.fold_left_map
              (fun checks (ctor_id, ctyp) ->
                let is_ctor = ngensym () in
                let ctor_json = ngensym () in
                let value = ngensym () in
                let check =
                  [
                    idecl l CT_bool is_ctor;
                    iextern l
                      (CL_id (is_ctor, CT_bool))
                      (mk_id "sail_config_object_has_key", [])
                      [V_id (json, CT_json); V_lit (VL_string (string_of_id ctor_id), CT_string)];
                  ]
                in
                let setup, call, cleanup = extract ctor_json ctyp in
                let ctor_setup, ctor_call, ctor_cleanup =
                  compile_funcall_with l ctx ctor_id
                    (fun cval -> ([], cval, []))
                    cval_ctyp
                    (fun _ -> None)
                    (fun _ -> None)
                    [V_id (value, ctyp)]
                in
                let extract =
                  [
                    idecl l CT_json ctor_json;
                    idecl l ctyp value;
                    iextern l
                      (CL_id (ctor_json, CT_json))
                      (mk_id "sail_config_object_key", [])
                      [V_id (json, CT_json); V_lit (VL_string (string_of_id ctor_id), CT_string)];
                  ]
                  @ setup @ ctor_setup
                  @ [call (CL_id (value, ctyp))]
                  @ [ctor_call (CL_id (variant_name, variant_ctyp))]
                  @ ctor_cleanup @ cleanup
                in
                (checks @ check, (is_ctor, extract))
              )
              [] constructors
          in
          let ctor_extracts =
            List.fold_left (fun rest (b, instrs) -> [iif l (V_id (b, CT_bool)) instrs rest]) [] ctor_extracts
          in
          ( [idecl l variant_ctyp variant_name] @ ctor_checks @ ctor_extracts,
            (fun clexp -> icopy l clexp (V_id (variant_name, variant_ctyp))),
            [iclear variant_ctyp variant_name]
          )
      | CT_struct (struct_id, args) as struct_ctyp ->
          let fields = instantiate_polymorphic_type ~at:l struct_id args ctx.records |> Bindings.bindings in
          let struct_name = ngensym () in
          let fields_from_json =
            List.map
              (fun (field_id, field_ctyp) ->
                let field_json = ngensym () in
                let setup, call, cleanup = extract field_json field_ctyp in
                [
                  idecl l CT_json field_json;
                  iextern l
                    (CL_id (field_json, CT_json))
                    (mk_id "sail_config_object_key", [])
                    [V_id (json, CT_json); V_lit (VL_string (string_of_id field_id), CT_string)];
                ]
                @ setup
                @ [call (CL_field (CL_id (struct_name, struct_ctyp), field_id, field_ctyp))]
                @ cleanup
                @ [iclear CT_json field_json]
              )
              fields
            |> List.concat
          in
          ( [idecl l struct_ctyp struct_name] @ fields_from_json,
            (fun clexp -> icopy l clexp (V_id (struct_name, struct_ctyp))),
            [iclear struct_ctyp struct_name]
          )
      | CT_vector item_ctyp ->
          let vec = ngensym () in
          let len = ngensym () in
          let n = ngensym () in
          let item_json = ngensym () in
          let item = ngensym () in
          let loop = label "config_vector_" in
          let index =
            V_call
              ( Isub,
                [
                  V_id (len, CT_fint 64);
                  V_call (Iadd, [V_id (n, CT_fint 64); V_lit (VL_int (Big_int.of_int 1), CT_fint 64)]);
                ]
              )
          in
          let setup, call, cleanup = extract item_json item_ctyp in
          ( [
              idecl l (CT_fint 64) len;
              iextern l (CL_id (len, CT_bool)) (mk_id "sail_config_list_length", []) [V_id (json, CT_json)];
              iif l
                (V_call (Eq, [V_id (len, CT_fint 64); V_lit (VL_int (Big_int.of_int (-1)), CT_fint 64)]))
                [ibad_config l]
                [];
              idecl l (CT_vector item_ctyp) vec;
              iextern l (CL_id (vec, CT_vector item_ctyp)) (mk_id "internal_vector_init", []) [V_id (len, CT_fint 64)];
              iinit l (CT_fint 64) n (V_lit (VL_int Big_int.zero, CT_fint 64));
              ilabel loop;
              idecl l CT_json item_json;
              iextern l
                (CL_id (item_json, CT_json))
                (mk_id "sail_config_list_nth", [])
                [V_id (json, CT_json); V_id (n, CT_fint 64)];
              idecl l item_ctyp item;
            ]
            @ setup
            @ [
                call (CL_id (item, item_ctyp));
                iextern l
                  (CL_id (vec, CT_vector item_ctyp))
                  (mk_id "internal_vector_update", [])
                  [V_id (vec, CT_vector item_ctyp); index; V_id (item, item_ctyp)];
              ]
            @ cleanup
            @ [
                iclear item_ctyp item;
                iclear CT_json item_json;
                icopy l
                  (CL_id (n, CT_fint 64))
                  (V_call (Iadd, [V_id (n, CT_fint 64); V_lit (VL_int (Big_int.of_int 1), CT_fint 64)]));
                ijump l (V_call (Ilt, [V_id (n, CT_fint 64); V_id (len, CT_fint 64)])) loop;
              ],
            (fun clexp -> icopy l clexp (V_id (vec, CT_vector item_ctyp))),
            [iclear (CT_vector item_ctyp) vec]
          )
      | CT_list item_ctyp ->
          let list = ngensym () in
          let len = ngensym () in
          let n = ngensym () in
          let item_json = ngensym () in
          let item = ngensym () in
          let loop_start = label "config_list_start_" in
          let loop_end = label "config_list_end_" in
          let index =
            V_call
              ( Isub,
                [
                  V_id (len, CT_fint 64);
                  V_call (Iadd, [V_id (n, CT_fint 64); V_lit (VL_int (Big_int.of_int 1), CT_fint 64)]);
                ]
              )
          in
          let setup, call, cleanup = extract item_json item_ctyp in
          ( [
              idecl l (CT_fint 64) len;
              iextern l (CL_id (len, CT_bool)) (mk_id "sail_config_list_length", []) [V_id (json, CT_json)];
              iif l
                (V_call (Eq, [V_id (len, CT_fint 64); V_lit (VL_int (Big_int.of_int (-1)), CT_fint 64)]))
                [ibad_config l]
                [];
              idecl l (CT_list item_ctyp) list;
              iinit l (CT_fint 64) n (V_lit (VL_int Big_int.zero, CT_fint 64));
              ilabel loop_start;
              ijump l (V_call (Igteq, [V_id (n, CT_fint 64); V_id (len, CT_fint 64)])) loop_end;
              idecl l CT_json item_json;
              iextern l (CL_id (item_json, CT_json)) (mk_id "sail_config_list_nth", []) [V_id (json, CT_json); index];
              idecl l item_ctyp item;
            ]
            @ setup
            @ [
                call (CL_id (item, item_ctyp));
                iextern l
                  (CL_id (list, CT_list item_ctyp))
                  (mk_id "sail_cons", [])
                  [V_id (item, item_ctyp); V_id (list, CT_list item_ctyp)];
              ]
            @ cleanup
            @ [
                iclear item_ctyp item;
                iclear CT_json item_json;
                icopy l
                  (CL_id (n, CT_fint 64))
                  (V_call (Iadd, [V_id (n, CT_fint 64); V_lit (VL_int (Big_int.of_int 1), CT_fint 64)]));
                igoto loop_start;
                ilabel loop_end;
              ],
            (fun clexp -> icopy l clexp (V_id (list, CT_list item_ctyp))),
            [iclear (CT_list item_ctyp) list]
          )
      | ctyp -> Reporting.unreachable l __POS__ ("Invalid configuration type " ^ string_of_ctyp ctyp)
    in

    let setup, call, cleanup = extract json ctyp in
    if ctx.no_static then (init @ setup, call, cleanup @ [iclear CT_json json; iclear CT_json_key key_name])
    else
      static_load l ctyp (fun s ->
          init @ setup @ [call (CL_id (s, ctyp))] @ cleanup @ [iclear CT_json json; iclear CT_json_key key_name]
      )

  let compile_config l ctx args typ =
    let ctyp = ctyp_of_typ ctx typ in
    let key =
      List.map
        (function
          | AV_lit (L_aux (L_string part, _), _) -> part
          | _ -> Reporting.unreachable l __POS__ "Invalid argument when compiling config key"
          )
        args
    in
    compile_config' l ctx key ctyp

  let rec compile_match ctx (AP_aux (apat_aux, { env; loc = l; _ })) cval on_failure =
    let ctx = { ctx with local_env = env } in
    let ctyp = cval_ctyp cval in
    let binding_ctyp typ =
      let semantic_ctyp = ctyp_of_typ ctx typ in
      if C.representation_refines ~semantic:semantic_ctyp ~represented:ctyp then ctyp else semantic_ctyp
    in
    match apat_aux with
    | AP_global (pid, typ) ->
        let global_ctyp = ctyp_of_typ ctx typ in
        ([], [icopy l (CL_id (name pid, global_ctyp)) cval], [], ctx)
    | AP_id (Name (pid, _), _) when is_ct_enum ctyp -> (
        match Env.lookup_id pid ctx.tc_env with
        | Unbound _ -> ([], [idecl l ctyp (name pid); icopy l (CL_id (name pid, ctyp)) cval], [], ctx)
        | _ -> ([on_failure l (V_call (Neq, [V_member (pid, ctyp); cval]))], [], [], ctx)
      )
    | AP_id (pid, typ) ->
        let id_ctyp = binding_ctyp typ in
        let ctx = { ctx with locals = NameMap.add pid (Immutable, id_ctyp) ctx.locals } in
        ([], [idecl l id_ctyp pid; icopy l (CL_id (pid, id_ctyp)) cval], [iclear id_ctyp pid], ctx)
    | AP_as (apat, id, typ) ->
        let id_ctyp = binding_ctyp typ in
        let pre, instrs, cleanup, ctx = compile_match ctx apat cval on_failure in
        let ctx = { ctx with locals = NameMap.add id (Immutable, id_ctyp) ctx.locals } in
        (pre, instrs @ [idecl l id_ctyp id; icopy l (CL_id (id, id_ctyp)) cval], iclear id_ctyp id :: cleanup, ctx)
    | AP_struct (afpats, _) ->
        let _, field_ctyp = struct_fields l ctx ctyp in
        let fold (pre, instrs, cleanup, ctx) (field, apat) =
          let pre', instrs', cleanup', ctx =
            compile_match ctx apat (V_field (cval, field, field_ctyp field)) on_failure
          in
          (pre @ pre', instrs @ instrs', cleanup' @ cleanup, ctx)
        in
        let pre, instrs, cleanup, ctx = List.fold_left fold ([], [], [], ctx) afpats in
        (pre, instrs, cleanup, ctx)
    | AP_tuple apats -> (
        let get_tup n = V_tuple_member (cval, List.length apats, n) in
        let fold (pre, instrs, cleanup, n, ctx) apat ctyp =
          let pre', instrs', cleanup', ctx = compile_match ctx apat (get_tup n) on_failure in
          (pre @ pre', instrs @ instrs', cleanup' @ cleanup, n + 1, ctx)
        in
        match ctyp with
        | CT_tup ctyps ->
            let pre, instrs, cleanup, _, ctx = List.fold_left2 fold ([], [], [], 0, ctx) apats ctyps in
            (pre, instrs, cleanup, ctx)
        | _ -> Reporting.unreachable l __POS__ ("AP_tuple with ctyp " ^ string_of_ctyp ctyp)
      )
    | AP_app (Newtype_wrapper _, apat, _) -> compile_match ctx apat cval on_failure
    | AP_app (Constructor ctor, apat, variant_typ) -> (
        match ctyp with
        | CT_variant (var_id, args) ->
            (* These should really be the same, something has gone wrong if they are not. *)
            if not (ctyp_equal (cval_ctyp cval) (ctyp_of_typ ctx variant_typ)) then
              raise
                (Reporting.err_general l
                   (Printf.sprintf "When compiling constructor pattern, %s should have the same type as %s"
                      (string_of_ctyp (cval_ctyp cval))
                      (string_of_ctyp (ctyp_of_typ ctx variant_typ))
                   )
                );
            let ctor_ctyp =
              let ctors = instantiate_polymorphic_type ~at:l var_id args ctx.variants in
              match Bindings.find_opt ctor ctors with
              | Some ctyp -> ctyp
              | None ->
                  Reporting.unreachable l __POS__
                    ("Failed to find constructor " ^ string_of_id ctor ^ " in " ^ string_of_ctyp ctyp)
            in
            let pre, instrs, cleanup, ctx =
              compile_match ctx apat (V_ctor_unwrap (cval, (ctor, args), ctor_ctyp)) on_failure
            in
            ([on_failure l (V_ctor_kind (cval, (ctor, args)))] @ pre, instrs, cleanup, ctx)
        | ctyp ->
            raise
              (Reporting.err_general l
                 (Printf.sprintf "Variant constructor %s : %s matching against non-variant type %s : %s"
                    (string_of_id ctor) (string_of_typ variant_typ) (string_of_cval cval) (string_of_ctyp ctyp)
                 )
              )
      )
    | AP_wild _ -> ([], [], [], ctx)
    | AP_cons (hd_apat, tl_apat) -> (
        match ctyp with
        | CT_list ctyp ->
            let hd_pre, hd_setup, hd_cleanup, ctx = compile_match ctx hd_apat (V_call (List_hd, [cval])) on_failure in
            let tl_pre, tl_setup, tl_cleanup, ctx = compile_match ctx tl_apat (V_call (List_tl, [cval])) on_failure in
            ( [on_failure l (V_call (List_is_empty, [cval]))] @ hd_pre @ tl_pre,
              hd_setup @ tl_setup,
              tl_cleanup @ hd_cleanup,
              ctx
            )
        | _ -> raise (Reporting.err_general l "Tried to pattern match cons on non list type")
      )
    | AP_nil _ -> ([on_failure l (V_call (Bnot, [V_call (List_is_empty, [cval])]))], [], [], ctx)
    | AP_vector_concat (vc_apats, typ) ->
        let vc_apats, total_width =
          List.fold_right
            (fun (width, apat) (result, offset) -> ((width, offset, apat) :: result, width + offset))
            vc_apats ([], 0)
        in
        List.fold_left
          (fun (pre, instrs, cleanup, ctx) (width, offset, apat) ->
            if (width <= 64 && total_width <= 64) || C.ignore_64 then (
              let pre', instrs', cleanup', ctx =
                compile_match ctx apat
                  (V_call (Slice width, [cval; V_lit (VL_int (Big_int.of_int offset), CT_fint 64)]))
                  on_failure
              in
              (pre @ pre', instrs @ instrs', cleanup' @ cleanup, ctx)
            )
            else (
              let sliced = ngensym () in
              let offset_id = ngensym () in
              let width_id = ngensym () in
              let mk_slice =
                [
                  idecl l CT_lbits sliced;
                  iinit l CT_lint offset_id (V_lit (VL_int (Big_int.of_int offset), CT_fint 64));
                  iinit l CT_lint width_id (V_lit (VL_int (Big_int.of_int width), CT_fint 64));
                  iextern l
                    (CL_id (sliced, CT_lbits))
                    (mk_id "slice", [])
                    [cval; V_id (offset_id, CT_lint); V_id (width_id, CT_lint)];
                  iclear CT_lint width_id;
                  iclear CT_lint offset_id;
                ]
              in
              let pre', instrs', cleanup', ctx = compile_match ctx apat (V_id (sliced, CT_lbits)) on_failure in
              (pre @ pre', instrs @ mk_slice @ instrs', cleanup' @ [iclear CT_lbits sliced] @ cleanup, ctx)
            )
          )
          ([], [], [], ctx) vc_apats

  let rec compile_alexp ctx alexp =
    match alexp with
    | AL_id (id, typ) ->
        let ctyp = match get_variable_ctyp id ctx with Some (_, ctyp) -> ctyp | None -> ctyp_of_typ ctx typ in
        CL_id (id, ctyp)
    | AL_addr (id, typ) ->
        let ctyp = match get_variable_ctyp id ctx with Some (_, ctyp) -> ctyp | None -> ctyp_of_typ ctx typ in
        CL_addr (CL_id (id, ctyp))
    | AL_field (alexp, field_id) ->
        let clexp = compile_alexp ctx alexp in
        let _, field_ctyp = struct_fields (id_loc field_id) ctx (clexp_ctyp clexp) in
        CL_field (compile_alexp ctx alexp, field_id, field_ctyp field_id)

  let can_optimize_control_flow_order ctx =
    match ctx.def_annot with
    | Some def_annot -> Option.is_some (get_def_attribute "optimize_control_flow_order" def_annot)
    | None -> false

  (** Returns true if we have an infalliable mapping case. This occurs only if the final case is marked with
      $[mapping_last] by the mappings.ml rewrite, and we have a $[mapping_infallible] attribute attached to the
      containing function in the context. *)
  let has_infallible_mapping_case ctx = function
    | [] -> true
    | cases ->
        let in_infallible_mapping =
          match ctx.def_annot with
          | None -> false
          | Some def_annot -> Option.is_some (get_def_attribute "mapping_infallible" def_annot)
        in
        in_infallible_mapping
        &&
        let _, _, _, uannot = Util.last cases in
        Option.is_some (get_attribute "mapping_last" uannot)

  let represented_aval_ctyp ctx aval =
    match aval with
    | AV_cval (cval, _) -> cval_ctyp cval
    | AV_id (id, typ) -> (
        match get_variable_ctyp id ctx with Some (_, ctyp) -> ctyp | None -> ctyp_of_typ ctx (lvar_typ typ)
      )
    | _ -> ctyp_of_typ ctx (aval_typ aval)

  let external_call_id ctx = function
    | Sail_function id -> Some (if ctx_is_extern id ctx then mk_id (ctx_get_extern id ctx) else id)
    | Pure_extern (id, _) | Extern (id, _) -> Some id
    | _ -> None

  let newtype_id_of_wrapper env wrapper_id =
    match Env.union_constructor_info wrapper_id env with
    | Some (_, _, newtype_id, _) when Env.is_newtype newtype_id env -> newtype_id
    | _ -> wrapper_id

  let rec demanded_newtype_representation env binding_id semantic = function
    | AE_aux (AE_typ (body, _), _) -> demanded_newtype_representation env binding_id semantic body
    | AE_aux (AE_app (Newtype_wrapper wrapper_id, [AV_id (body_id, _)], _), _) when Name.compare binding_id body_id = 0
      ->
        let newtype_id = newtype_id_of_wrapper env wrapper_id in
        let represented = C.specialize_newtype_payload newtype_id semantic in
        if C.propagate_newtype_payload_representation newtype_id ~semantic ~represented then Some represented else None
    | AE_aux (AE_app (Newtype_wrapper wrapper_id, [AV_cval (V_id (body_id, _), _)], _), _)
      when Name.compare binding_id body_id = 0 ->
        let newtype_id = newtype_id_of_wrapper env wrapper_id in
        let represented = C.specialize_newtype_payload newtype_id semantic in
        if C.propagate_newtype_payload_representation newtype_id ~semantic ~represented then Some represented else None
    | _ -> None

  let rec compile_aexp ctx (AE_aux (aexp_aux, { env; loc = l; uannot })) =
    let ctx = { ctx with local_env = env } in
    match aexp_aux with
    | AE_let (mut, id, binding_typ, binding, (AE_aux (_, { env = body_env; _ }) as body), body_typ) ->
        let semantic_binding_ctyp = ctyp_of_typ { ctx with local_env = body_env } binding_typ in
        let represented_aval local_representations ctx = function
          | (AV_id (id, _) | AV_cval (V_id (id, _), _)) as aval -> (
              match NameMap.find_opt id local_representations with
              | Some represented -> represented
              | None -> represented_aval_ctyp ctx aval
            )
          | aval -> represented_aval_ctyp ctx aval
        in
        let rec represented_expression local_representations semantic = function
          | AE_aux (AE_typ (body, _), _) -> represented_expression local_representations semantic body
          | AE_aux (AE_let (_, id, binding_typ, binding, body, _), { env; _ }) ->
              let binding_semantic = ctyp_of_typ { ctx with local_env = env } binding_typ in
              let binding_represented = represented_expression local_representations binding_semantic binding in
              let local_representations =
                if C.representation_refines ~semantic:binding_semantic ~represented:binding_represented then
                  NameMap.add id binding_represented local_representations
                else local_representations
              in
              represented_expression local_representations semantic body
          | AE_aux (AE_block (_, body, _), _) -> represented_expression local_representations semantic body
          | AE_aux (AE_val aval, _) ->
              let represented = represented_aval local_representations ctx aval in
              if C.representation_refines ~semantic ~represented then represented else semantic
          | AE_aux (AE_app (call, args, _), _) -> (
              match external_call_id ctx call with
              | Some id ->
                  C.specialize_call_result id (List.map (represented_aval local_representations ctx) args) semantic
              | None -> semantic
            )
          | AE_aux (AE_field (record, field, _), { env; loc; _ }) -> (
              let field_ctx = { ctx with local_env = env } in
              match represented_aval local_representations field_ctx record with
              | CT_struct _ as record_ctyp ->
                  let _, field_ctyp = struct_fields loc field_ctx record_ctyp in
                  let represented = field_ctyp field in
                  if C.representation_refines ~semantic ~represented then represented else semantic
              | _ -> semantic
            )
          | _ -> semantic
        in
        let represented_binding () = represented_expression NameMap.empty semantic_binding_ctyp binding in
        let binding_ctyp =
          match mut with
          | Mutable ->
              (* ANF introduces mutable temporaries for nested primitive calls
                 even when the source expression is pure.  Preserve the same
                 proved representation choices here as for immutable lets;
                 otherwise a field-derived byte pointer is immediately
                 converted back to its semantic integer coordinate before it
                 reaches the enclosing function call. *)
              let represented = represented_binding () in
              if C.propagate_anf_temporary_representation ~semantic:semantic_binding_ctyp ~represented then represented
              else semantic_binding_ctyp
          | Immutable -> (
              match demanded_newtype_representation body_env id semantic_binding_ctyp body with
              | Some represented -> represented
              | None -> represented_binding ()
            )
        in
        let setup, call, cleanup = compile_aexp ctx binding in
        let letb_setup, letb_cleanup =
          ( [idecl l binding_ctyp id; iblock1 (setup @ [call (CL_id (id, binding_ctyp))] @ cleanup)],
            [iclear binding_ctyp id]
          )
        in
        let ctx = { ctx with locals = NameMap.add id (mut, binding_ctyp) ctx.locals } in
        let setup, call, cleanup = compile_aexp ctx body in
        (letb_setup @ setup, call, cleanup @ letb_cleanup)
    | AE_app (Sail_function id, vs, _) ->
        if Option.is_some (get_attribute "mapping_guarded" uannot) then (
          let override_id = append_id id "_infallible" in
          if Bindings.mem override_id ctx.valspecs then compile_funcall ~override_id l ctx id vs
          else compile_funcall l ctx id vs
        )
        else compile_funcall l ctx id vs
    | AE_app (Newtype_wrapper id, args, _) -> (
        match args with
        | [arg] ->
            let setup, cval, cleanup = compile_aval l ctx arg in
            (setup, (fun clexp -> icopy l clexp cval), cleanup)
        | _ -> Reporting.unreachable l __POS__ "Found newtype wrapper with > 1 argument during Jib generation"
      )
    | AE_app (Pure_extern (id, return_typ), args, typ) ->
        let return_ctyp = Option.map (ctyp_of_typ ctx) return_typ in
        compile_extern l ctx id args typ return_ctyp
    | AE_app (Extern (id, return_typ), args, typ) ->
        let str = string_of_id id in
        if str = "sail_assert" && C.erase_assert_messages then (
          match args with
          | [cond; _msg] ->
              let cond_setup, cond_cval, cond_cleanup = compile_aval l ctx cond in
              (cond_setup, (fun clexp -> iextern l clexp (mk_id "__sail_fixed_assert", []) [cond_cval]), cond_cleanup)
          | _ -> Reporting.unreachable l __POS__ "Bad arity for sail_assert"
        )
        else if str = "sail_assert" && C.assert_to_exception then (
          match args with
          | [cond; msg] ->
              let cond_setup, cond_cval, cond_cleanup = compile_aval l ctx cond in
              let msg_setup, msg_cval, _ = compile_aval l ctx msg in
              let exn_setup, exn_cval = assert_exception l msg_cval in
              ( cond_setup @ [iif l cond_cval [] (msg_setup @ exn_setup @ [ithrow l exn_cval])] @ cond_cleanup,
                (fun clexp -> icopy l clexp unit_cval),
                []
              )
          | _ -> Reporting.unreachable l __POS__ "Bad arity for sail_assert"
        )
        else if str = "sail_config_get" then compile_config l ctx args typ
        else (
          let return_ctyp = Option.map (ctyp_of_typ ctx) return_typ in
          compile_extern l ctx id args typ return_ctyp
        )
    | AE_val aval ->
        let setup, cval, cleanup = compile_aval l ctx aval in
        (setup, (fun clexp -> icopy l clexp cval), cleanup)
    (* Compile case statements *)
    | AE_match (aval, cases, typ)
      when C.eager_control_flow
           && (can_optimize_control_flow_order ctx || Option.is_some (get_attribute "anf_pure" uannot)) ->
        let ctyp = ctyp_of_typ ctx typ in
        let aval_setup, cval, aval_cleanup = compile_aval l ctx aval in
        let compile_case case_match_id case_return_id (apat, guard, body, case_uannot) =
          if is_dead_aexp body then None
          else (
            let trivial_guard =
              match guard with
              | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _)
              | AE_aux (AE_val (AV_cval (V_lit (VL_bool true, CT_bool), _)), _) ->
                  true
              | _ -> false
            in
            let pre_destructure, destructure, destructure_cleanup, ctx =
              compile_match ctx apat cval (fun l b -> icopy l (CL_id (case_match_id, CT_bool)) (V_call (Bnot, [b])))
            in
            let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
            let body_setup, body_call, body_cleanup = compile_aexp ctx body in
            Some
              ([idecl l ctyp case_return_id; iinit l CT_bool case_match_id (V_lit (VL_bool true, CT_bool))]
              @ pre_destructure @ destructure
              @ ( if not trivial_guard then (
                    let gs = ngensym () in
                    guard_setup
                    @ [
                        idecl l CT_bool gs;
                        guard_call (CL_id (gs, CT_bool));
                        icopy l
                          (CL_id (case_match_id, CT_bool))
                          (V_call (Band, [V_id (case_match_id, CT_bool); V_id (gs, CT_bool)]));
                      ]
                    @ guard_cleanup
                  )
                  else []
                )
              @ body_setup
              @ [body_call (CL_id (case_return_id, ctyp))]
              @ body_cleanup @ destructure_cleanup
              )
          )
        in
        let case_ids, cases =
          List.filter_map
            (fun case ->
              let open Util.Option_monad in
              let case_match_id = ngensym () in
              let case_return_id = ngensym () in
              let* case = compile_case case_match_id case_return_id case in
              Some ((V_id (case_match_id, CT_bool), V_id (case_return_id, ctyp)), case)
            )
            cases
          |> List.split
        in
        let rec build_ite = function
          | [(_, ret)] -> ret
          | (b, ret) :: rest -> V_call (Ite, [b; ret; build_ite rest])
          | [] -> Reporting.unreachable l __POS__ "Empty match found"
        in
        (aval_setup @ List.concat cases, (fun clexp -> icopy l clexp (build_ite case_ids)), aval_cleanup)
    | AE_match (aval, cases, typ) ->
        let is_complete = Option.is_some (get_attribute "complete" uannot) || has_infallible_mapping_case ctx cases in
        let ctx = update_coverage_override uannot ctx in
        let ctyp = ctyp_of_typ ctx typ in
        let aval_setup, cval, aval_cleanup = compile_aval l ctx aval in
        (* Get the number of cases, because we don't want to check branch
           coverage for matches with only a single case. *)
        let num_cases = List.length cases in
        let branch_id, on_reached = if num_cases > 1 then coverage_branch_reached ctx l else (0, []) in
        let case_return_id = ngensym () in
        let finish_match_label = label "finish_match_" in
        let compile_case is_last (apat, guard, body, case_uannot) =
          let case_label = label "case_" in
          if is_dead_aexp body then [ilabel case_label]
          else (
            let trivial_guard =
              match guard with
              | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _)
              | AE_aux (AE_val (AV_cval (V_lit (VL_bool true, CT_bool), _)), _) ->
                  true
              | _ -> false
            in
            (* If we are at the last case of a complete match, the final destructuring can never fail
               so just make it a no-op. Note that it is important we do this, rather than just keep the
               jump that is never taken, otherwise we confuse targets like Sail->SV which linearize the
               control flow graph. *)
            let pre_destructure, destructure, destructure_cleanup, ctx =
              compile_match ctx apat cval (fun l b ->
                  if is_last && is_complete then icomment "complete" else ijump l b case_label
              )
            in
            let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
            let body_setup, body_call, body_cleanup = compile_aexp ctx body in
            let gs = ngensym () in
            let case_instrs =
              pre_destructure @ destructure
              @ ( if not trivial_guard then
                    guard_setup
                    @ [idecl l CT_bool gs; guard_call (CL_id (gs, CT_bool))]
                    @ guard_cleanup
                    @ [iif l (V_call (Bnot, [V_id (gs, CT_bool)])) (destructure_cleanup @ [igoto case_label]) []]
                  else []
                )
              @ (if num_cases > 1 then coverage_branch_target_taken ctx branch_id body else [])
              @ body_setup
              @ [body_call (CL_id (case_return_id, ctyp))]
              @ body_cleanup @ destructure_cleanup
              @ [igoto finish_match_label]
            in
            [iblock case_instrs; ilabel case_label]
          )
        in
        ( aval_setup @ on_reached
          @ [idecl l ctyp case_return_id]
          @ List.concat (Util.map_last compile_case cases)
          @ (if is_complete then [] else [imatch_failure l])
          @ [ilabel finish_match_label],
          (fun clexp -> icopy l clexp (V_id (case_return_id, ctyp))),
          [iclear ctyp case_return_id] @ aval_cleanup
        )
    (* Compile try statement *)
    | AE_try (aexp, cases, typ) ->
        let is_complete = Option.is_some (get_attribute "complete" uannot) || has_infallible_mapping_case ctx cases in
        let ctyp = ctyp_of_typ ctx typ in
        let aexp_setup, aexp_call, aexp_cleanup = compile_aexp ctx aexp in
        let try_return_id = ngensym () in
        let post_exception_handlers_label = label "post_exception_handlers_" in
        let exn_cval = V_id (current_exception, ctyp_of_typ ctx (mk_typ (Typ_id (mk_id "exception")))) in
        let compile_case is_last (apat, guard, body, case_uannot) =
          let trivial_guard =
            match guard with
            | AE_aux (AE_val (AV_lit (L_aux (L_true, _), _)), _)
            | AE_aux (AE_val (AV_cval (V_lit (VL_bool true, CT_bool), _)), _) ->
                true
            | _ -> false
          in
          let try_label = label "try_" in
          let pre_destructure, destructure, destructure_cleanup, ctx =
            compile_match ctx apat exn_cval (fun l b ->
                if is_last && is_complete then icomment "complete" else ijump l b try_label
            )
          in
          let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard in
          let body_setup, body_call, body_cleanup = compile_aexp ctx body in
          let gs = ngensym () in
          let case_instrs =
            pre_destructure @ destructure
            @ ( if not trivial_guard then
                  guard_setup
                  @ [idecl l CT_bool gs; guard_call (CL_id (gs, CT_bool))]
                  @ guard_cleanup
                  @ [ijump l (V_call (Bnot, [V_id (gs, CT_bool)])) try_label]
                else []
              )
            @ body_setup
            @ [body_call (CL_id (try_return_id, ctyp))]
            @ body_cleanup @ destructure_cleanup
            @ [igoto post_exception_handlers_label]
          in
          [iblock case_instrs; ilabel try_label]
        in
        assert (ctyp_equal ctyp (ctyp_of_typ ctx typ));
        ( [
            idecl l ctyp try_return_id;
            itry_block l (aexp_setup @ [aexp_call (CL_id (try_return_id, ctyp))] @ aexp_cleanup);
            ijump l (V_call (Bnot, [V_id (have_exception, CT_bool)])) post_exception_handlers_label;
            icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool false, CT_bool));
          ]
          @ ( if C.assert_to_exception then
                [
                  iif l
                    (V_ctor_kind (exn_cval, (mk_id "__assertion_failed#", [])))
                    []
                    [
                      icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool true, CT_bool));
                      igoto post_exception_handlers_label;
                    ];
                ]
              else []
            )
          @ List.concat (Util.map_last compile_case cases)
          @ ( if is_complete then []
              else [(* fallthrough *) icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool true, CT_bool))]
            )
          @ [ilabel post_exception_handlers_label],
          (fun clexp -> icopy l clexp (V_id (try_return_id, ctyp))),
          []
        )
    | AE_if (aval, then_aexp, else_aexp, if_typ) ->
        let ctx = update_coverage_override uannot ctx in
        if is_dead_aexp then_aexp then compile_aexp ctx else_aexp
        else if is_dead_aexp else_aexp then compile_aexp ctx then_aexp
        else (
          let if_ctyp = ctyp_of_typ ctx if_typ in
          let setup, cval, cleanup = compile_aval l ctx aval in
          let pure_attr = get_attribute "anf_pure" uannot in
          let eager = C.eager_control_flow && (can_optimize_control_flow_order ctx || Option.is_some pure_attr) in
          if eager then (
            let then_gs = ngensym () in
            let then_setup, then_call, then_cleanup = compile_aexp ctx then_aexp in
            let else_gs = ngensym () in
            let else_setup, else_call, else_cleanup = compile_aexp ctx else_aexp in
            ( setup @ then_setup @ else_setup
              @ [
                  idecl l if_ctyp then_gs;
                  idecl l if_ctyp else_gs;
                  then_call (CL_id (then_gs, if_ctyp));
                  else_call (CL_id (else_gs, if_ctyp));
                ],
              (fun clexp -> icopy l clexp (V_call (Ite, [cval; V_id (then_gs, if_ctyp); V_id (else_gs, if_ctyp)]))),
              [iclear if_ctyp else_gs; iclear if_ctyp then_gs] @ else_cleanup @ then_cleanup @ cleanup
            )
          )
          else (
            let branch_id, on_reached = coverage_branch_reached ctx l in
            let compile_branch aexp =
              let setup, call, cleanup = compile_aexp ctx aexp in
              fun clexp -> coverage_branch_target_taken ctx branch_id aexp @ setup @ [call clexp] @ cleanup
            in
            ( setup,
              (fun clexp ->
                append_into_block on_reached
                  (iif l cval (compile_branch then_aexp clexp) (compile_branch else_aexp clexp))
              ),
              cleanup
            )
          )
        )
    (* FIXME: AE_struct_update could be AV_record_update - would reduce some copying. *)
    | AE_struct_update (aval, fields, typ) ->
        let ctyp = ctyp_of_typ ctx typ in
        let _, field_ctyp = struct_fields l ctx ctyp in
        let gs = ngensym () in
        let compile_fields (id, aval) =
          let field_setup, cval, field_cleanup = compile_aval l ctx aval in
          field_setup @ [icopy l (CL_field (CL_id (gs, ctyp), id, field_ctyp id)) cval] @ field_cleanup
        in
        let setup, cval, cleanup = compile_aval l ctx aval in
        ( [idecl l ctyp gs]
          @ setup
          @ [icopy l (CL_id (gs, ctyp)) cval]
          @ cleanup
          @ List.concat (List.map compile_fields (Bindings.bindings fields)),
          (fun clexp -> icopy l clexp (V_id (gs, ctyp))),
          [iclear ctyp gs]
        )
    | AE_short_circuit (SC_and, aval, aexp) ->
        let left_setup, cval, left_cleanup = compile_aval l ctx aval in
        let right_setup, call, right_cleanup = compile_aexp ctx aexp in
        if
          C.eager_control_flow
          && (can_optimize_control_flow_order ctx || Option.is_some (get_attribute "anf_pure" uannot))
        then (
          let gs = ngensym () in
          ( left_setup @ right_setup @ [idecl l CT_bool gs; call (CL_id (gs, CT_bool))],
            (fun clexp -> icopy l clexp (V_call (Band, [cval; V_id (gs, CT_bool)]))),
            right_cleanup @ left_cleanup
          )
        )
        else (
          let ctx = update_coverage_override uannot ctx in
          let branch_id, on_reached = coverage_branch_reached ctx l in
          let right_coverage = coverage_branch_target_taken ctx branch_id aexp in
          let gs = ngensym () in
          ( left_setup @ on_reached
            @ [
                idecl l CT_bool gs;
                iif l cval
                  (right_coverage @ right_setup @ [call (CL_id (gs, CT_bool))] @ right_cleanup)
                  [icopy l (CL_id (gs, CT_bool)) (V_lit (VL_bool false, CT_bool))];
              ]
            @ left_cleanup,
            (fun clexp -> icopy l clexp (V_id (gs, CT_bool))),
            []
          )
        )
    | AE_short_circuit (SC_or, aval, aexp) ->
        let left_setup, cval, left_cleanup = compile_aval l ctx aval in
        let right_setup, call, right_cleanup = compile_aexp ctx aexp in
        if
          C.eager_control_flow
          && (can_optimize_control_flow_order ctx || Option.is_some (get_attribute "anf_pure" uannot))
        then (
          let gs = ngensym () in
          ( left_setup @ right_setup @ [idecl l CT_bool gs; call (CL_id (gs, CT_bool))],
            (fun clexp -> icopy l clexp (V_call (Bor, [cval; V_id (gs, CT_bool)]))),
            right_cleanup @ left_cleanup
          )
        )
        else (
          let ctx = update_coverage_override uannot ctx in
          let branch_id, on_reached = coverage_branch_reached ctx l in
          let right_coverage = coverage_branch_target_taken ctx branch_id aexp in
          let gs = ngensym () in
          ( left_setup @ on_reached
            @ [
                idecl l CT_bool gs;
                iif l cval
                  [icopy l (CL_id (gs, CT_bool)) (V_lit (VL_bool true, CT_bool))]
                  (right_coverage @ right_setup @ [call (CL_id (gs, CT_bool))] @ right_cleanup);
              ]
            @ left_cleanup,
            (fun clexp -> icopy l clexp (V_id (gs, CT_bool))),
            []
          )
        )
    (* This is a faster assignment rule for updating fields of a
       struct. *)
    | AE_assign (AL_id (id, assign_typ), AE_aux (AE_struct_update (AV_id (rid, _), fields, typ), _))
      when Name.compare id rid = 0 ->
        let ctyp = ctyp_of_typ ctx typ in
        let _, field_ctyp = struct_fields l ctx ctyp in
        let compile_fields (field_id, aval) =
          let field_setup, cval, field_cleanup = compile_aval l ctx aval in
          field_setup @ [icopy l (CL_field (CL_id (id, ctyp), field_id, field_ctyp field_id)) cval] @ field_cleanup
        in
        (List.concat (List.map compile_fields (Bindings.bindings fields)), (fun clexp -> icopy l clexp unit_cval), [])
    | AE_assign (alexp, aexp) ->
        let setup, call, cleanup = compile_aexp ctx aexp in
        (setup @ [call (compile_alexp ctx alexp)], (fun clexp -> icopy l clexp unit_cval), cleanup)
    | AE_block (aexps, aexp, _) ->
        let block = compile_block ctx aexps in
        let setup, call, cleanup = compile_aexp ctx aexp in
        (block @ setup, call, cleanup)
    | AE_loop (While, cond, body) ->
        let loop_start_label = label "while_" in
        let loop_end_label = label "wend_" in
        let cond_setup, cond_call, cond_cleanup = compile_aexp ctx cond in
        let body_setup, body_call, body_cleanup = compile_aexp ctx body in
        let gs = ngensym () in
        let unit_gs = ngensym () in
        let loop_test = V_call (Bnot, [V_id (gs, CT_bool)]) in
        ( [idecl l CT_bool gs; idecl l CT_unit unit_gs]
          @ [ilabel loop_start_label]
          @ [
              iblock
                (cond_setup
                @ [cond_call (CL_id (gs, CT_bool))]
                @ cond_cleanup
                @ [ijump l loop_test loop_end_label]
                @ body_setup
                @ [body_call (CL_id (unit_gs, CT_unit))]
                @ body_cleanup
                @ [igoto loop_start_label]
                );
            ]
          @ [ilabel loop_end_label],
          (fun clexp -> icopy l clexp unit_cval),
          []
        )
    | AE_loop (Until, cond, body) ->
        let loop_start_label = label "repeat_" in
        let loop_end_label = label "until_" in
        let cond_setup, cond_call, cond_cleanup = compile_aexp ctx cond in
        let body_setup, body_call, body_cleanup = compile_aexp ctx body in
        let gs = ngensym () in
        let unit_gs = ngensym () in
        let loop_test = V_id (gs, CT_bool) in
        ( [idecl l CT_bool gs; idecl l CT_unit unit_gs]
          @ [ilabel loop_start_label]
          @ [
              iblock
                (body_setup
                @ [body_call (CL_id (unit_gs, CT_unit))]
                @ body_cleanup @ cond_setup
                @ [cond_call (CL_id (gs, CT_bool))]
                @ cond_cleanup
                @ [ijump l loop_test loop_end_label]
                @ [igoto loop_start_label]
                );
            ]
          @ [ilabel loop_end_label],
          (fun clexp -> icopy l clexp unit_cval),
          []
        )
    | AE_typ (aexp, typ) -> compile_aexp ctx aexp
    | AE_return (aval, typ) ->
        let fn_return_ctyp =
          match Env.get_ret_typ env with
          | Some typ -> ctyp_of_typ ctx typ
          | None -> raise (Reporting.err_general l "No function return type found when compiling return statement")
        in
        (* Cleanup info will be re-added by fix_early_(heap/stack)_return *)
        let return_setup, cval, _ = compile_aval l ctx aval in
        let creturn =
          if ctyp_equal fn_return_ctyp (cval_ctyp cval) then [ireturn cval]
          else (
            let gs = ngensym () in
            [idecl l fn_return_ctyp gs; icopy l (CL_id (gs, fn_return_ctyp)) cval; ireturn (V_id (gs, fn_return_ctyp))]
          )
        in
        (return_setup @ creturn, (fun clexp -> icomment "unreachable after return"), [])
    | AE_throw (aval, typ) ->
        (* Cleanup info will be handled by fix_exceptions *)
        let throw_setup, cval, _ = compile_aval l ctx aval in
        (throw_setup @ [ithrow l cval], (fun clexp -> icomment "unreachable after throw"), [])
    | AE_exit (aval, typ) ->
        let exit_setup, cval, _ = compile_aval l ctx aval in
        (exit_setup @ [iexit l], (fun clexp -> icomment "unreachable after exit"), [])
    | AE_field (aval, id, typ) ->
        let setup, cval, cleanup = compile_aval l ctx aval in
        let _, field_ctyp = struct_fields l ctx (cval_ctyp cval) in
        (setup, (fun clexp -> icopy l clexp (V_field (cval, id, field_ctyp id))), cleanup)
    (* If unrolling is enabled, and all the loop bounds are fixed then just unroll the exact required amount *)
    | AE_for
        ( loop_var,
          AE_aux (AE_val (AV_lit (L_aux (L_num loop_from, _), _)), _),
          AE_aux (AE_val (AV_lit (L_aux (L_num loop_to, _), _)), _),
          AE_aux (AE_val (AV_lit (L_aux (L_num loop_step, _), _)), _),
          Ord_aux (ord, _),
          body
        )
      when Option.is_some C.unroll_loops ->
        let literal_fits_int64 value = Big_int.less_equal (min_int 64) value && Big_int.less_equal value (max_int 64) in
        let loop_ctyp =
          if literal_fits_int64 loop_from && literal_fits_int64 loop_to && literal_fits_int64 loop_step then CT_fint 64
          else CT_lint
        in
        let ctx = { ctx with locals = NameMap.add loop_var (Immutable, loop_ctyp) ctx.locals } in

        let is_inc = match ord with Ord_inc -> true | Ord_dec -> false in

        let body_setup, body_call, body_cleanup = compile_aexp ctx body in
        let body_gs = ngensym () in

        let loop_iteration i =
          let loop_body () =
            [icopy l (CL_id (loop_var, loop_ctyp)) (V_lit (VL_int i, loop_ctyp))]
            @ body_setup
            @ [body_call (CL_id (body_gs, CT_unit))]
            @ body_cleanup
          in
          if is_inc then
            if Big_int.greater i loop_to then None else Some (Big_int.add i loop_step, iblock (loop_body ()))
          else if Big_int.less i loop_to then None
          else Some (Big_int.sub i loop_step, iblock (loop_body ()))
        in
        let rec unroll acc i =
          match loop_iteration i with None -> List.rev acc | Some (next, instr) -> unroll (instr :: acc) next
        in

        ( [idecl l loop_ctyp loop_var; idecl l CT_unit body_gs] @ unroll [] loop_from,
          (fun clexp -> icopy l clexp unit_cval),
          []
        )
    | AE_for (loop_var, loop_from, loop_to, loop_step, Ord_aux (ord, _), body) ->
        let loop_ctyp =
          if foreach_int64_proven ctx.local_env (aexp_typ loop_from) (aexp_typ loop_to) (aexp_typ loop_step) ord then
            CT_fint 64
          else CT_lint
        in
        let ctx = { ctx with locals = NameMap.add loop_var (Immutable, loop_ctyp) ctx.locals } in

        let is_inc = match ord with Ord_inc -> true | Ord_dec -> false in

        (* Loop variables *)
        let from_setup, from_call, from_cleanup = compile_aexp ctx loop_from in
        let from_gs = ngensym () in
        let to_setup, to_call, to_cleanup = compile_aexp ctx loop_to in
        let to_gs = ngensym () in
        let step_setup, step_call, step_cleanup = compile_aexp ctx loop_step in
        let step_gs = ngensym () in
        let variable_init gs setup call cleanup =
          [idecl l loop_ctyp gs; iblock (setup @ [call (CL_id (gs, loop_ctyp))] @ cleanup)]
        in

        let loop_start_label = label "for_start_" in
        let loop_end_label = label "for_end_" in
        let body_setup, body_call, body_cleanup = compile_aexp ctx body in
        let body_gs = ngensym () in

        let loop_body prefix continue =
          prefix
          @ [
              iblock
                ([
                   ijump l
                     (V_call ((if is_inc then Igt else Ilt), [V_id (loop_var, loop_ctyp); V_id (to_gs, loop_ctyp)]))
                     loop_end_label;
                 ]
                @ body_setup
                @ [body_call (CL_id (body_gs, CT_unit))]
                @ body_cleanup
                @ [
                    icopy l
                      (CL_id (loop_var, loop_ctyp))
                      (V_call
                         ( ( if ctyp_equal loop_ctyp (CT_fint 64) then if is_inc then Proven_iadd else Proven_isub
                             else if is_inc then Iadd
                             else Isub
                           ),
                           [V_id (loop_var, loop_ctyp); V_id (step_gs, loop_ctyp)]
                         )
                      );
                  ]
                @ continue ()
                );
            ]
        in
        (* We can either generate an actual loop body for C, or unroll the body for SMT *)
        let actual = loop_body [ilabel loop_start_label] (fun () -> [igoto loop_start_label]) in
        let rec unroll max n = loop_body [] (fun () -> if n < max then unroll max (n + 1) else [imatch_failure l]) in
        let body =
          match (get_attribute "unroll" uannot, C.unroll_loops) with
          | Some attr_data_opt, Some _ -> (
              match attr_data_opt with
              | _, Some (AD_aux (AD_num times, _)) -> unroll (Big_int.to_int times) 0
              | _, Some (AD_aux (_, l)) -> raise (Reporting.err_general l "Invalid argument on unroll attribute")
              | l, None -> raise (Reporting.err_general l "Expected numeric argument for unroll attribute")
            )
          | None, Some times -> unroll times 0
          | _ -> actual
        in

        ( variable_init from_gs from_setup from_call from_cleanup
          @ variable_init to_gs to_setup to_call to_cleanup
          @ variable_init step_gs step_setup step_call step_cleanup
          @ [
              iblock
                ([
                   idecl l loop_ctyp loop_var;
                   icopy l (CL_id (loop_var, loop_ctyp)) (V_id (from_gs, loop_ctyp));
                   idecl l CT_unit body_gs;
                 ]
                @ body
                @ [ilabel loop_end_label]
                );
            ],
          (fun clexp -> icopy l clexp unit_cval),
          []
        )

  and compile_block ctx = function
    | [] -> []
    | (AE_aux (_, { loc = l; _ }) as exp) :: exps ->
        let setup, call, cleanup = compile_aexp ctx exp in
        let rest = compile_block ctx exps in
        if C.use_void then setup @ [call (CL_void CT_unit)] @ cleanup @ rest
        else (
          let gs = ngensym () in
          setup @ [idecl l CT_unit gs; call (CL_id (gs, CT_unit))] @ cleanup @ rest
        )

  let fast_int = function CT_lint when !optimize_aarch64_fast_struct -> CT_fint 64 | ctyp -> ctyp

  (** Compile a sail type definition into a IR one. Most of the actual work of translating the typedefs into C is done
      by the code generator, as it's easy to keep track of structs, tuples and unions in their sail form at this level,
      and leave the fiddly details of how they get mapped to C in the next stage. This function also adds details of the
      types it compiles to the context, ctx, which is why it returns a ctypdef * ctx pair. **)
  let compile_type_def ctx (TD_aux (type_def, (l, _))) =
    match type_def with
    | TD_enum (id, members, _) ->
        let ids = List.map fst members in
        (Some (CTD_enum (id, ids)), { ctx with enums = Bindings.add id (IdSet.of_list ids) ctx.enums })
    | TD_record (id, typq, ctors, _) ->
        let record_ctx = { ctx with local_env = Env.add_typquant l typq ctx.local_env } in
        let ctors =
          List.fold_left
            (fun ctors ((field_id, typ), _) ->
              let ctyp = fast_int (ctyp_of_typ record_ctx typ) in
              Bindings.add field_id (C.specialize_struct_field id field_id ctyp) ctors
            )
            Bindings.empty ctors
        in
        let params = quant_kopts typq |> List.filter is_typ_kopt |> List.map kopt_kid in
        ( Some (CTD_struct (id, params, Bindings.bindings ctors)),
          { ctx with records = Bindings.add id (params, ctors) ctx.records }
        )
    | TD_variant (id, typq, tus, is_newtype) ->
        let compile_tu = function
          | Tu_aux (Tu_ty_id (typ, ctor_id), _) ->
              let ctx = { ctx with local_env = Env.add_typquant (id_loc ctor_id) typq ctx.local_env } in
              let ctyp = ctyp_of_typ ctx typ in
              let ctyp = if is_newtype then C.specialize_newtype_payload id ctyp else ctyp in
              (ctyp, ctor_id)
        in
        let tus =
          if string_of_id id = "exception" && C.assert_to_exception then
            tus @ [Tu_aux (Tu_ty_id (string_typ, mk_id "__assertion_failed#"), mk_def_annot (gen_loc l) ())]
          else tus
        in
        let ctus =
          List.fold_left (fun ctus (ctyp, id) -> Bindings.add id ctyp ctus) Bindings.empty (List.map compile_tu tus)
        in
        let params = quant_kopts typq |> List.filter is_typ_kopt |> List.map kopt_kid in
        ( Some (CTD_variant (id, params, Bindings.bindings ctus)),
          { ctx with variants = Bindings.add id (params, ctus) ctx.variants }
        )
    (* All type abbreviations are filtered out in compile_def  *)
    | TD_abbrev (id, typq, arg) -> (
        match arg with
        | A_aux (A_typ typ, _) when string_of_id id <> "bits" && not (List.exists is_typ_kopt (quant_kopts typq)) ->
            let abbrev_ctx = { ctx with local_env = Env.add_typquant l typq ctx.local_env } in
            let ctyp = ctyp_of_typ abbrev_ctx typ in
            (Some (CTD_abbrev (id, ctyp)), ctx)
        | _ -> (None, ctx)
      )
    | TD_abstract (id, K_aux (kind, _), inst) -> (
        let compile_inst ctyp = function
          | TDC_key key ->
              (* The abstract initialisers are ran very early, before the rest of the model,
                 so we can't rely on Jib static initialisers being set up. *)
              let setup, call, cleanup = compile_config' l { ctx with no_static = true } key ctyp in
              CTDI_instrs (setup @ [call (CL_id (Abstract id, ctyp))] @ cleanup)
          | TDC_none -> CTDI_none
        in
        let is_initialised = function CTDI_instrs _ -> Initialised | CTDI_none -> Uninitialised in
        match kind with
        | K_int ->
            let ctyp = ctyp_of_typ ctx (atom_typ (nid id)) in
            let inst = compile_inst ctyp inst in
            ( Some (CTD_abstract (id, ctyp, inst)),
              { ctx with abstracts = Bindings.add id (ctyp, is_initialised inst) ctx.abstracts }
            )
        | K_bool ->
            let inst = compile_inst CT_bool inst in
            ( Some (CTD_abstract (id, CT_bool, inst)),
              { ctx with abstracts = Bindings.add id (CT_bool, is_initialised inst) ctx.abstracts }
            )
        | _ -> Reporting.unreachable l __POS__ "Found abstract type that was neither an integer nor a boolean"
      )
    (* Will be re-written before here, see bitfield.ml *)
    | TD_bitfield _ -> Reporting.unreachable l __POS__ "Cannot compile TD_bitfield"

  let generate_cleanup instrs =
    let generate_cleanup' (I_aux (instr, _)) =
      match instr with
      | I_init (ctyp, id, cval) -> [(id, iclear ctyp id)]
      | I_decl (ctyp, id) -> [(id, iclear ctyp id)]
      | instr -> []
    in
    let is_clear ids = function I_aux (I_clear (_, id), _) -> NameSet.add id ids | _ -> ids in
    let cleaned = List.fold_left is_clear NameSet.empty instrs in
    instrs |> List.map generate_cleanup' |> List.concat
    |> List.filter (fun (id, _) -> not (NameSet.mem id cleaned))
    |> List.map snd

  let fix_exception_block ?(return = None) ctx instrs =
    let end_block_label = label "end_block_exception_" in
    let is_exception_stop (I_aux (instr, _)) =
      match instr with I_throw _ | I_if _ | I_block _ | I_funcall _ -> true | _ -> false
    in
    (* In this function 'after' is instructions after the one we've
       matched on, 'before is instructions before the instruction we've
       matched with, but after the previous match, and 'historic' are
       all the befores from previous matches. *)
    let rec rewrite_exception historic instrs =
      match instr_split_at is_exception_stop instrs with
      | instrs, [] -> instrs
      | before, I_aux (I_block instrs, _) :: after ->
          before @ [iblock (rewrite_exception (historic @ before) instrs)] @ rewrite_exception (historic @ before) after
      | before, I_aux (I_if (cval, then_instrs, else_instrs), (_, l)) :: after ->
          let historic = historic @ before in
          before
          @ [iif l cval (rewrite_exception historic then_instrs) (rewrite_exception historic else_instrs)]
          @ rewrite_exception historic after
      | before, I_aux (I_throw cval, (_, l)) :: after ->
          before
          @ [
              icopy l (CL_id (current_exception, cval_ctyp cval)) cval;
              icopy l (CL_id (have_exception, CT_bool)) (V_lit (VL_bool true, CT_bool));
            ]
          @ ( if C.track_throw then (
                let loc_string = Reporting.short_loc_to_string l in
                [icopy l (CL_id (throw_location, CT_string)) (V_lit (VL_string loc_string, CT_string))]
              )
              else []
            )
          @ generate_cleanup (historic @ before)
          @ [igoto end_block_label]
          @ rewrite_exception (historic @ before) after
      | before, (I_aux (I_funcall (x, _, f, args), (_, l)) as funcall) :: after ->
          let effects =
            match Bindings.find_opt (fst f) ctx.effect_info.functions with
            | Some effects -> effects
            (* Constructors and back-end built-in value operations might not be present *)
            | None -> Effects.EffectSet.empty
          in
          if Effects.throws effects then
            before
            @ [
                funcall;
                iif l
                  (V_id (have_exception, CT_bool))
                  (generate_cleanup (historic @ before) @ [igoto end_block_label])
                  [];
              ]
            @ rewrite_exception (historic @ before) after
          else before @ (funcall :: rewrite_exception (historic @ before) after)
      | _, _ -> assert false (* unreachable *)
    in
    match return with
    | None -> rewrite_exception [] instrs @ [ilabel end_block_label]
    | Some ctyp -> rewrite_exception [] instrs @ [ilabel end_block_label; iundefined ctyp]

  let rec map_try_block f (I_aux (instr, aux)) =
    let instr =
      match instr with
      | I_decl _ | I_reset _ | I_init _ | I_reinit _ -> instr
      | I_if (cval, instrs1, instrs2) ->
          I_if (cval, List.map (map_try_block f) instrs1, List.map (map_try_block f) instrs2)
      | I_funcall _ | I_copy _ | I_clear _ | I_throw _ | I_return _ -> instr
      | I_block instrs -> I_block (List.map (map_try_block f) instrs)
      | I_try_block instrs -> I_try_block (f (List.map (map_try_block f) instrs))
      | I_comment _ | I_label _ | I_goto _ | I_raw _ | I_jump _ | I_exit _ | I_undefined _ | I_end _ -> instr
    in
    I_aux (instr, aux)

  let fix_exception ?(return = None) ctx instrs =
    let instrs = List.map (map_try_block (fix_exception_block ctx)) instrs in
    fix_exception_block ~return ctx instrs

  let rec compile_arg_pat ctx label (P_aux (p_aux, (l, _)) as pat) ctyp =
    let source_type = string_of_typ (typ_of_pat pat) in
    let destructured_arg_name () = match IdSet.elements (pat_ids pat) with [id] -> string_of_id id | _ -> "arg" in
    match p_aux with
    | P_id id -> (name id, ([], []), ctx)
    | P_wild ->
        let gs = ngensym ~source_name:"unused" ~source_type () in
        (gs, ([], []), ctx)
    | P_tuple [] | P_lit (L_aux (L_unit, _)) ->
        let gs = ngensym ~source_name:"unused" ~source_type () in
        (gs, ([], []), ctx)
    | P_var (pat, _) -> compile_arg_pat ctx label pat ctyp
    | P_typ (_, pat) -> compile_arg_pat ctx label pat ctyp
    | _ ->
        let apat = anf_pat pat in
        let gs = ngensym ~source_name:(destructured_arg_name ()) ~source_type () in
        let pre_destructure, destructure, cleanup, ctx = compile_match ctx apat (V_id (gs, ctyp)) label in
        (gs, (pre_destructure @ destructure, cleanup), ctx)

  let rec compile_arg_pats ctx label (P_aux (p_aux, (l, _)) as pat) ctyps =
    match p_aux with
    | P_typ (_, pat) -> compile_arg_pats ctx label pat ctyps
    | P_tuple pats when List.length pats = List.length ctyps ->
        let ctx, compiled_args =
          List.fold_left2
            (fun (ctx, compiled_args) pat ctyp ->
              let arg_id, destructure, ctx = compile_arg_pat ctx label pat ctyp in
              (ctx, (arg_id, destructure) :: compiled_args)
            )
            (ctx, []) pats ctyps
        in
        ([], List.rev compiled_args, [], ctx)
    | _ when List.length ctyps = 1 ->
        let arg_id, destructure, ctx = compile_arg_pat ctx label pat (List.nth ctyps 0) in
        ([], [(arg_id, destructure)], [], ctx)
    | _ ->
        let arg_id, (destructure, cleanup), ctx = compile_arg_pat ctx label pat (CT_tup ctyps) in
        let new_ids =
          List.mapi
            (fun i ctyp -> (ngensym ~source_name:("arg_" ^ string_of_int i) ~source_type:(string_of_ctyp ctyp) (), ctyp))
            ctyps
        in
        ( destructure
          @ [idecl l (CT_tup ctyps) arg_id]
          @ List.mapi
              (fun i (id, ctyp) -> icopy l (CL_tuple (CL_id (arg_id, CT_tup ctyps), i)) (V_id (id, ctyp)))
              new_ids,
          List.map (fun (id, _) -> (id, ([], []))) new_ids,
          [iclear (CT_tup ctyps) arg_id] @ cleanup,
          ctx
        )

  let combine_destructure_cleanup xs = (List.concat (List.map fst xs), List.concat (List.rev (List.map snd xs)))

  let fix_destructure l fail_label = function
    | [], cleanup -> ([], cleanup)
    | destructure, cleanup ->
        let body_label = label "fundef_body_" in
        (destructure @ [igoto body_label; ilabel fail_label; imatch_failure l; ilabel body_label], cleanup)

  (** Functions that have heap-allocated return types are implemented by passing a pointer a location where the return
      value should be stored. The ANF -> Sail IR pass for expressions simply outputs an I_return instruction for any
      return value, so this function walks over the IR ast for expressions and modifies the return statements into code
      that sets that pointer, as well as adds extra control flow to cleanup heap-allocated variables correctly when a
      function terminates early. See the generate_cleanup function for how this is done. *)
  let fix_early_return l ret instrs =
    let end_function_label = label "end_function_" in
    let is_return_recur (I_aux (instr, _)) =
      match instr with I_return _ | I_undefined _ | I_if _ | I_block _ | I_try_block _ -> true | _ -> false
    in
    let rec rewrite_return historic instrs =
      match instr_split_at is_return_recur instrs with
      | instrs, [] -> instrs
      | before, I_aux (I_try_block instrs, (_, l)) :: after ->
          before @ [itry_block l (rewrite_return (historic @ before) instrs)] @ rewrite_return (historic @ before) after
      | before, I_aux (I_block instrs, _) :: after ->
          before @ [iblock (rewrite_return (historic @ before) instrs)] @ rewrite_return (historic @ before) after
      | before, I_aux (I_if (cval, then_instrs, else_instrs), (_, l)) :: after ->
          let historic = historic @ before in
          before
          @ [iif l cval (rewrite_return historic then_instrs) (rewrite_return historic else_instrs)]
          @ rewrite_return historic after
      | before, I_aux (I_return cval, (_, l)) :: after ->
          let cleanup_label = label "cleanup_" in
          let end_cleanup_label = label "end_cleanup_" in
          before
          @ [icopy l ret cval; igoto cleanup_label]
          (* This is probably dead code until cleanup_label, but we cannot be sure there are no jumps into it. *)
          @ rewrite_return (historic @ before) after
          @ [igoto end_cleanup_label; ilabel cleanup_label]
          @ generate_cleanup (historic @ before)
          @ [igoto end_function_label; ilabel end_cleanup_label]
      | before, I_aux (I_undefined _, (_, l)) :: after ->
          let cleanup_label = label "cleanup_" in
          let end_cleanup_label = label "end_cleanup_" in
          before
          @ [igoto cleanup_label]
          @ rewrite_return (historic @ before) after
          @ [igoto end_cleanup_label; ilabel cleanup_label]
          @ generate_cleanup (historic @ before)
          @ [igoto end_function_label; ilabel end_cleanup_label]
      | _, _ -> assert false
    in
    rewrite_return [] instrs @ [ilabel end_function_label; iend l]

  (** This pass ensures that all variables created by I_decl have unique names *)
  let unique_names =
    let unique_id ctyp = function
      | Name (id, _) -> ngensym ~source_name:(string_of_id id) ~source_type:(string_of_ctyp ctyp) ()
      | Gen (_, _, _, source_name, source_type) -> ngensym ?source_name ?source_type ()
      | _ -> ngensym ~source_name:"value" ~source_type:(string_of_ctyp ctyp) ()
    in

    let rec opt seen = function
      | I_aux (I_decl (ctyp, id), aux) :: instrs when NameSet.mem id seen ->
          let id' = unique_id ctyp id in
          let instrs', seen = opt seen instrs in
          (I_aux (I_decl (ctyp, id'), aux) :: instrs_rename id id' instrs', seen)
      | I_aux (I_decl (ctyp, id), aux) :: instrs ->
          let instrs', seen = opt (NameSet.add id seen) instrs in
          (I_aux (I_decl (ctyp, id), aux) :: instrs', seen)
      | I_aux (I_block block, aux) :: instrs ->
          let block', seen = opt seen block in
          let instrs', seen = opt seen instrs in
          (I_aux (I_block block', aux) :: instrs', seen)
      | I_aux (I_try_block block, aux) :: instrs ->
          let block', seen = opt seen block in
          let instrs', seen = opt seen instrs in
          (I_aux (I_try_block block', aux) :: instrs', seen)
      | I_aux (I_if (cval, then_instrs, else_instrs), aux) :: instrs ->
          let then_instrs', seen = opt seen then_instrs in
          let else_instrs', seen = opt seen else_instrs in
          let instrs', seen = opt seen instrs in
          (I_aux (I_if (cval, then_instrs', else_instrs'), aux) :: instrs', seen)
      | instr :: instrs ->
          let instrs', seen = opt seen instrs in
          (instr :: instrs', seen)
      | [] -> ([], seen)
    in
    fun instrs -> fst (opt NameSet.empty instrs)

  let letdef_count = ref 0

  let compile_fun_to_wires ctx (def_annot : unit Ast.def_annot) id slots =
    let l = gen_loc def_annot.loc in

    (* Find the function's type. *)
    let quant, Typ_aux (fn_typ, _) =
      try Env.get_val_spec id ctx.local_env with Type_error.Type_error _ -> Env.get_val_spec id ctx.tc_env
    in
    let params = quant_kopts quant |> List.filter is_typ_kopt |> List.map kopt_kid in

    let arg_typs, ret_typ = match fn_typ with Typ_fn (arg_typs, ret_typ) -> (arg_typs, ret_typ) | _ -> assert false in

    let ctx = { ctx with local_env = Env.add_typquant (id_loc id) quant ctx.tc_env } in

    let arg_ctyps =
      List.mapi
        (fun n typ ->
          (name (mk_id ("a" ^ string_of_int n)), C.specialize_declared_function_argument id n (ctyp_of_typ ctx typ))
        )
        arg_typs
    in
    let ret_ctyp = C.specialize_declared_function_result id (ctyp_of_typ ctx ret_typ) in

    let num_args = List.length arg_ctyps in

    let funwire_name = function
      | Arg n -> name (append_id id (Printf.sprintf "_fw_arg%d#" n))
      | Ret -> name (append_id id "_fw_ret#")
      | Invoke -> name (append_id id "_fw_invoke#")
    in

    let funwire_attr_info = function
      | Arg n -> AD_aux (AD_num (Big_int.of_int n), l)
      | Ret -> AD_aux (AD_string "return", l)
      | Invoke -> AD_aux (AD_string "invoke", l)
    in

    let funwire_attr fw =
      mk_def_annot
        ~attrs:
          [(l, "funwire", Some (AD_aux (AD_list [AD_aux (AD_string (string_of_id id), l); funwire_attr_info fw], l)))]
        l ()
    in

    let funwire_ctyp = function Arg n -> snd (List.nth arg_ctyps n) | Ret -> ret_ctyp | Invoke -> CT_bool in

    let slotvector ctyp = if slots > 1 then CT_fvector (slots, ctyp) else ctyp in

    let mk_register fw =
      CDEF_aux (CDEF_register (funwire_name fw, slotvector (funwire_ctyp fw), []), funwire_attr fw)
    in

    let read_slot fw slot =
      if slots > 1 then V_call (Index slot, [V_id (funwire_name fw, CT_fvector (slots, funwire_ctyp fw))])
      else V_id (funwire_name fw, funwire_ctyp fw)
    in

    let write_slot fw slot cval =
      if slots > 1 then (
        let vector_ctyp = CT_fvector (slots, funwire_ctyp fw) in
        iextern l
          (CL_id (funwire_name fw, vector_ctyp))
          (mk_id "internal_vector_update", [])
          [V_id (funwire_name fw, vector_ctyp); V_lit (VL_int (Big_int.of_int slot), CT_fint 64); cval]
      )
      else icopy l (CL_id (funwire_name fw, funwire_ctyp fw)) (V_id (funwire_name fw, funwire_ctyp fw))
    in

    let updates =
      List.init slots (fun slot ->
          [
            iif l
              (V_call (Bnot, [read_slot Invoke slot]))
              ([write_slot Invoke slot (V_lit (VL_bool true, CT_bool))]
              @ List.mapi (fun n (arg, ctyp) -> write_slot (Arg n) slot (V_id (arg, ctyp))) arg_ctyps
              @ [icopy l (CL_id (return, ret_ctyp)) (read_slot Ret slot); iend l]
              )
              [];
          ]
      )
      |> List.concat
    in

    let exn_setup, exn_cval =
      assert_exception l (V_lit (VL_string ("reached unreachable in " ^ string_of_id id), CT_string))
    in

    [mk_register Invoke]
    @ List.init num_args (fun n -> mk_register (Arg n))
    @ [mk_register Ret]
    @ [
        CDEF_aux (CDEF_val (id, params, List.map snd arg_ctyps, ret_ctyp, None), def_annot);
        CDEF_aux
          ( CDEF_fundef
              ( id,
                Return_plain,
                List.map fst arg_ctyps,
                fix_exception ~return:(Some ret_ctyp) ctx (updates @ exn_setup @ [ithrow l exn_cval])
              ),
            mk_def_annot l ()
          );
      ]

  type compiled_def = Compiled of cdef list | Parallel of (unit -> cdef list)

  let compile_funcl ctx def_annot id pat guard exp =
    let debug_attr = get_def_attribute "jib_debug" def_annot in
    let mapping_function_attr = get_def_attribute "mapping_function" def_annot in
    let test_no_gmp = get_def_attribute "test_no_gmp" def_annot in

    if Option.is_some debug_attr then (
      let extra = if Option.is_some mapping_function_attr then " (mapping)" else "" in
      prerr_endline Util.("Rewritten source for " ^ string_of_id id ^ extra ^ ":" |> yellow |> bold |> clear);
      prerr_endline (Document.to_string (Pretty_print_sail.doc_exp (Type_check.strip_exp exp)))
    );

    (* Find the function's type. *)
    let quant, Typ_aux (fn_typ, _) =
      try Env.get_val_spec id ctx.local_env with Type_error.Type_error _ -> Env.get_val_spec id ctx.tc_env
    in
    let params = quant_kopts quant |> List.filter is_typ_kopt |> List.map kopt_kid in

    let arg_typs, ret_typ = match fn_typ with Typ_fn (arg_typs, ret_typ) -> (arg_typs, ret_typ) | _ -> assert false in

    (* Handle the argument pattern. *)
    let fundef_label = label "fundef_fail_" in
    let orig_ctx = ctx in
    (* The context must be updated before we call ctyp_of_typ on the argument types. *)
    let ctx = { ctx with local_env = Env.add_typquant (id_loc id) quant ctx.local_env } in
    let ctx = update_coverage_override_def def_annot ctx in

    let arg_ctyps =
      List.mapi (fun index typ -> C.specialize_declared_function_argument id index (ctyp_of_typ ctx typ)) arg_typs
    in
    let ret_ctyp = C.specialize_declared_function_result id (ctyp_of_typ ctx ret_typ) in

    (* Now we have enough information to compute the return context for this compilation step. *)
    let return_ctx =
      match mapping_function_attr with
      | Some _ ->
          let id = append_id id "_infallible" in
          { orig_ctx with valspecs = Bindings.add id (None, arg_ctyps, ret_ctyp, empty_uannot) orig_ctx.valspecs }
      | None -> orig_ctx
    in

    let do_funcl_compilation () =
      (* Compile the function arguments as patterns. *)
      let arg_setup, compiled_args, arg_cleanup, ctx =
        compile_arg_pats ctx (fun l b -> ijump l b fundef_label) pat arg_ctyps
      in
      let ctx =
        (* We need the primop analyzer to be aware of the function argument types, so put them in ctx *)
        List.fold_left2
          (fun ctx (id, _) ctyp -> { ctx with locals = NameMap.add id (Immutable, ctyp) ctx.locals })
          ctx compiled_args arg_ctyps
      in

      let known_ids = IdSet.fold (fun id -> NameSet.add (name id)) (pat_ids pat) (letbind_ids ctx) in
      let guard_bindings = ref NameSet.empty in
      let guard_instrs =
        match guard with
        | Some guard ->
            let (AE_aux (_, { loc = l; _ }) as guard) = anf guard in
            guard_bindings := aexp_bindings guard;
            let guard_aexp = C.optimize_anf ctx (no_shadow known_ids guard) in
            let guard_setup, guard_call, guard_cleanup = compile_aexp ctx guard_aexp in
            let guard_label = label "guard_" in
            let gs = ngensym ~source_name:"guard" ~source_type:(string_of_typ bool_typ) () in
            [
              iblock
                ([idecl l CT_bool gs]
                @ guard_setup
                @ [guard_call (CL_id (gs, CT_bool))]
                @ guard_cleanup
                @ [ijump (id_loc id) (V_id (gs, CT_bool)) guard_label; imatch_failure l; ilabel guard_label]
                );
            ]
        | None -> []
      in

      (* Optimize and compile the expression to ANF. *)
      let aexp = C.optimize_anf ctx (no_shadow (NameSet.union known_ids !guard_bindings) (anf exp)) in

      if Option.is_some debug_attr then (
        prerr_endline Util.("ANF for " ^ string_of_id id ^ ":" |> yellow |> bold |> clear);
        prerr_endline (Document.to_string (pp_aexp aexp))
      );

      let compile_body ctx =
        let setup, call, cleanup = compile_aexp ctx aexp in
        let destructure, destructure_cleanup =
          compiled_args |> List.map snd |> combine_destructure_cleanup |> fix_destructure (id_loc id) fundef_label
        in

        let instrs =
          arg_setup @ destructure @ guard_instrs @ setup
          @ [call (CL_id (return, ret_ctyp))]
          @ cleanup @ destructure_cleanup @ arg_cleanup
        in
        let instrs = fix_early_return (exp_loc exp) (CL_id (return, ret_ctyp)) instrs in
        let instrs = unique_names instrs in
        let instrs = fix_exception ~return:(Some ret_ctyp) ctx instrs in
        coverage_function_entry ctx id (exp_loc exp) @ instrs
      in

      let compiled_args = List.map fst compiled_args in
      let instrs = compile_body ctx in

      if Option.is_some debug_attr then (
        let type_string = Util.string_of_list ", " string_of_ctyp arg_ctyps ^ " -> " ^ string_of_ctyp ret_ctyp in
        prerr_endline Util.("IR for " ^ string_of_id id ^ ": " ^ type_string |> yellow |> bold |> clear);
        List.iter (fun instr -> prerr_endline (string_of_instr instr)) instrs
      );

      if Option.is_some test_no_gmp then
        List.iter
          (fun instr ->
            iter_instr
              (function
                | I_aux (I_decl (ctyp, _), (_, l)) | I_aux (I_init (ctyp, _, _), (_, l)) ->
                    if ctyp_equal ctyp CT_lint || ctyp_equal ctyp CT_lbits then
                      raise (Reporting.err_general l "Found GMP large integer or bitvector with test_no_gmp attribute")
                | _ -> ()
                )
              instr
          )
          instrs;

      (* If the function is a mapping, we generate an infallible version (that never causes a match_failure) *)
      let mapping_infallible =
        match mapping_function_attr with
        | Some (attr_l, _) ->
            let instrs =
              compile_body
                { ctx with def_annot = Some (add_def_attribute (gen_loc attr_l) "mapping_infallible" None def_annot) }
            in
            let id = append_id id "_infallible" in
            [
              CDEF_aux (CDEF_val (id, params, arg_ctyps, ret_ctyp, None), def_annot);
              CDEF_aux (CDEF_fundef (id, Return_plain, compiled_args, instrs), def_annot);
            ]
        | None -> []
      in
      [CDEF_aux (CDEF_fundef (id, Return_plain, compiled_args, instrs), def_annot)] @ mapping_infallible
    in

    (Parallel do_funcl_compilation, return_ctx)

  (** Compile a Sail toplevel definition into an IR definition **)
  let rec compile_def n total ctx (DEF_aux (aux, _) as def) =
    let compiled, ctx = compile_def' n total ctx def in
    (compiled, { ctx with def_annot = None })

  and compile_def_force n total ctx def =
    match compile_def n total ctx def with Compiled cdefs, ctx -> (cdefs, ctx) | Parallel f, ctx -> (f (), ctx)

  and compile_def' n total ctx (DEF_aux (aux, def_annot) as def) =
    let def_env = def_annot.env in
    let def_annot = strip_def_annot def_annot in
    let ctx = { ctx with local_env = def_env; def_annot = Some def_annot } in
    match aux with
    | DEF_register (DEC_aux (DEC_reg (typ, id, None), _)) ->
        let ctyp = ctyp_of_typ ctx typ in
        ( Compiled [CDEF_aux (CDEF_register (name id, ctyp, []), def_annot)],
          { ctx with registers = Bindings.add id ctyp ctx.registers }
        )
    | DEF_register (DEC_aux (DEC_reg (typ, id, Some exp), _)) ->
        let ctyp = ctyp_of_typ ctx typ in
        let aexp = C.optimize_anf ctx (no_shadow (letbind_ids ctx) (anf exp)) in
        let setup, call, cleanup = compile_aexp ctx aexp in
        let instrs = setup @ [call (CL_id (name id, ctyp))] @ cleanup in
        let instrs = unique_names instrs in
        ( Compiled [CDEF_aux (CDEF_register (name id, ctyp, instrs), def_annot)],
          { ctx with registers = Bindings.add id ctyp ctx.registers }
        )
    | DEF_val (VS_aux (VS_val_spec (_, id, ext), _)) ->
        let quant, Typ_aux (fn_typ, _) = Env.get_val_spec id ctx.tc_env in
        let params = quant_kopts quant |> List.filter is_typ_kopt |> List.map kopt_kid in
        let extern =
          if Env.is_extern id ctx.tc_env ctx.target_name then Some (Env.get_extern id ctx.tc_env ctx.target_name)
          else None
        in
        let arg_typs, ret_typ =
          match fn_typ with Typ_fn (arg_typs, ret_typ) -> (arg_typs, ret_typ) | _ -> assert false
        in
        let generic_signature = generic_signature quant arg_typs ret_typ in
        let ctx' = { ctx with local_env = Env.add_typquant (id_loc id) quant ctx.local_env } in
        let arg_ctyps =
          List.mapi (fun index typ -> C.specialize_declared_function_argument id index (ctyp_of_typ ctx' typ)) arg_typs
        in
        let ret_ctyp = C.specialize_declared_function_result id (ctyp_of_typ ctx' ret_typ) in
        ( Compiled [CDEF_aux (CDEF_val (id, params, arg_ctyps, ret_ctyp, extern), def_annot)],
          {
            ctx with
            valspecs = Bindings.add id (extern, arg_ctyps, ret_ctyp, uannot_of_def_annot def_annot) ctx.valspecs;
            generic_signatures = Bindings.add id generic_signature ctx.generic_signatures;
          }
        )
    | DEF_fundef (FD_aux (FD_function (_, _, [FCL_aux (FCL_funcl (id, pexp), _)]), _)) -> (
        Util.progress "Compiling " (string_of_id id) n total;
        match Bindings.find_opt id C.fun_to_wires with
        | Some slots -> (Compiled (compile_fun_to_wires ctx def_annot id slots), ctx)
        | None -> (
            match pexp with
            | Pat_aux (Pat_exp (pat, exp), _) -> compile_funcl ctx def_annot id pat None exp
            | Pat_aux (Pat_when (pat, guard, exp), _) -> compile_funcl ctx def_annot id pat (Some guard) exp
          )
      )
    | DEF_fundef (FD_aux (FD_function (_, _, []), (l, _))) ->
        raise (Reporting.err_general l "Encountered function with no clauses")
    | DEF_fundef (FD_aux (FD_function (_, _, _ :: _ :: _), (l, _))) ->
        raise (Reporting.err_general l "Encountered function with multiple clauses")
    | DEF_type type_def ->
        let tdef_opt, ctx = compile_type_def ctx type_def in
        (Compiled (List.map (fun tdef -> CDEF_aux (CDEF_type tdef, def_annot)) (Option.to_list tdef_opt)), ctx)
    | DEF_let (pat, exp) ->
        let debug_attr = get_def_attribute "jib_debug" def_annot in
        let apat = anf_pat ~global:true pat in
        let globals = apat_globals apat in
        let ctyp =
          let semantic = ctyp_of_typ ctx (typ_of_pat pat) in
          match globals with [(id, _, _)] -> C.specialize_declared_function_result id semantic | _ -> semantic
        in
        let aexp = C.optimize_anf ctx (no_shadow (letbind_ids ctx) (anf exp)) in
        let setup, call, cleanup = compile_aexp ctx aexp in
        let gs = ngensym ~source_name:"let_value" ~source_type:(string_of_typ (typ_of_pat pat)) () in
        let end_label = label "let_end_" in
        let pre_destructure, destructure, destructure_cleanup, _ =
          compile_match ctx apat (V_id (gs, ctyp)) (fun l b -> ijump l b end_label)
        in
        let gs_setup, gs_cleanup = ([idecl (exp_loc exp) ctyp gs], [iclear ctyp gs]) in
        let bindings =
          List.map
            (fun (id, env, typ) ->
              let semantic = ctyp_of_typ { ctx with local_env = env } typ in
              (id, C.specialize_declared_function_result id semantic)
            )
            globals
        in
        let n = !letdef_count in
        incr letdef_count;
        let instrs =
          gs_setup @ setup
          @ [call (CL_id (gs, ctyp))]
          @ cleanup @ pre_destructure @ destructure @ destructure_cleanup @ gs_cleanup
          @ [ilabel end_label]
        in
        let instrs = unique_names instrs in
        if Option.is_some debug_attr then (
          prerr_endline Util.("IR for letbind " ^ string_of_int n |> yellow |> bold |> clear);
          prerr_endline
            (Util.string_of_list ", " (fun (id, ctyp) -> string_of_id id ^ " : " ^ string_of_ctyp ctyp) bindings);
          List.iter (fun instr -> prerr_endline (string_of_instr instr)) instrs
        );
        ( Compiled [CDEF_aux (CDEF_let (n, bindings, instrs), def_annot)],
          {
            ctx with
            letbinds = n :: ctx.letbinds;
            letbind_ctyps = List.fold_left (fun ids (id, ctyp) -> Bindings.add id ctyp ids) ctx.letbind_ctyps bindings;
          }
        )
    (* Only DEF_default that matters is default Order, but all order
       polymorphism is specialised by this point. *)
    | DEF_default _ -> (Compiled [], ctx)
    (* Overloading resolved by type checker *)
    | DEF_overload _ -> (Compiled [], ctx)
    (* Only the parser and sail pretty printer care about this. *)
    | DEF_fixity _ -> (Compiled [], ctx)
    | DEF_pragma ("abstract", Pragma_line (id_str, _)) ->
        (Compiled [CDEF_aux (CDEF_pragma ("abstract", id_str), def_annot)], ctx)
    | DEF_pragma ("c_in_main", Pragma_line (source, _)) ->
        (Compiled [CDEF_aux (CDEF_pragma ("c_in_main", source), def_annot)], ctx)
    | DEF_pragma ("c_in_main_post", Pragma_line (source, _)) ->
        (Compiled [CDEF_aux (CDEF_pragma ("c_in_main_post", source), def_annot)], ctx)
    (* We just ignore any pragmas we don't want to deal with. *)
    | DEF_pragma _ -> (Compiled [], ctx)
    (* Termination measures only needed for Coq, and other theorem prover output *)
    | DEF_measure _ -> (Compiled [], ctx)
    | DEF_loop_measures _ -> (Compiled [], ctx)
    | DEF_internal_mutrec fundefs ->
        let defs = List.map (fun fdef -> mk_def (DEF_fundef fdef) def_env) fundefs in
        let cdefs, ctx =
          List.fold_left
            (fun (cdefs, ctx) def ->
              let cdefs', ctx = compile_def_force n total ctx def in
              (cdefs @ cdefs', ctx)
            )
            ([], ctx) defs
        in
        (Compiled cdefs, ctx)
    | DEF_constraint _ -> (Compiled [], ctx)
    (* Scattereds, mapdefs, and event related definitions should be removed by this point *)
    | DEF_scattered _ | DEF_mapdef _ | DEF_outcome _ | DEF_impl _ | DEF_instantiation _ ->
        Reporting.unreachable (def_loc def) __POS__
          ("Could not compile:\n" ^ Document.to_string (Pretty_print_sail.doc_def (strip_def def)))

  let mangle_mono_id id ctx ctyps = append_id id ("<" ^ Util.string_of_list "," (mangle_string_of_ctyp ctx) ctyps ^ ">")

  (* The specialized calls argument keeps track of functions we have
     already specialized, so we don't accidentally specialize them twice
     in a future round of specialization *)
  let rec specialize_functions ?(specialized_calls = ref IdSet.empty) ctx cdefs =
    let polymorphic_functions =
      List.filter_map
        (function
          | CDEF_aux (CDEF_val (id, _, param_ctyps, ret_ctyp, _), _) ->
              if List.exists is_polymorphic param_ctyps || is_polymorphic ret_ctyp then Some id else None
          | _ -> None
          )
        cdefs
      |> IdSet.of_list
    in

    (* First we find all the 'monomorphic calls', places where a
       polymorphic function is applied to only concrete type arguments

       At each such location we remove the type arguments and mangle the
       call name using them *)
    let monomorphic_calls = ref Bindings.empty in
    let collect_monomorphic_calls = function
      | I_aux (I_funcall (clexp, extern, (id, ctyp_args), args), aux)
        when IdSet.mem id polymorphic_functions && not (List.exists is_polymorphic ctyp_args) ->
          monomorphic_calls :=
            Bindings.update id
              (function
                | None -> Some (CTListSet.singleton ctyp_args) | Some calls -> Some (CTListSet.add ctyp_args calls)
                )
              !monomorphic_calls;
          I_aux (I_funcall (clexp, extern, (mangle_mono_id id ctx ctyp_args, []), args), aux)
      | instr -> instr
    in
    let cdefs = List.rev_map (cdef_map_instr collect_monomorphic_calls) cdefs |> List.rev in

    (* Now we duplicate function defintions and type declarations for
       each of the monomorphic calls we just found. *)
    let spec_tyargs = ref Bindings.empty in
    let rec specialize_fundefs ctx prior = function
      | (CDEF_aux (CDEF_val (id, tyargs, param_ctyps, ret_ctyp, extern), def_annot) as orig_cdef) :: cdefs
        when Bindings.mem id !monomorphic_calls ->
          spec_tyargs := Bindings.add id tyargs !spec_tyargs;
          let specialized_specs =
            List.filter_map
              (fun instantiation ->
                let specialized_id = mangle_mono_id id ctx instantiation in
                if not (IdSet.mem specialized_id !specialized_calls) then (
                  let substs =
                    List.fold_left2
                      (fun substs tyarg ty -> KBindings.add tyarg ty substs)
                      KBindings.empty tyargs instantiation
                  in
                  let param_ctyps = List.map (subst_poly substs) param_ctyps in
                  let ret_ctyp = subst_poly substs ret_ctyp in
                  Some (CDEF_aux (CDEF_val (specialized_id, [], param_ctyps, ret_ctyp, extern), def_annot))
                )
                else None
              )
              (CTListSet.elements (Bindings.find id !monomorphic_calls))
          in
          let ctx =
            let source_generic_signature = Bindings.find_opt id ctx.generic_signatures in
            List.fold_left
              (fun ctx cdef ->
                match cdef with
                | CDEF_aux (CDEF_val (specialized_id, _, param_ctyps, ret_ctyp, _), def_annot) ->
                    let generic_signatures =
                      match source_generic_signature with
                      | Some signature -> Bindings.add specialized_id signature ctx.generic_signatures
                      | None -> ctx.generic_signatures
                    in
                    {
                      ctx with
                      valspecs =
                        Bindings.add specialized_id
                          (extern, param_ctyps, ret_ctyp, uannot_of_def_annot def_annot)
                          ctx.valspecs;
                      generic_signatures;
                    }
                | cdef -> ctx
              )
              ctx specialized_specs
          in
          specialize_fundefs ctx ((orig_cdef :: specialized_specs) @ prior) cdefs
      | (CDEF_aux (CDEF_fundef (id, heap_return, params, body), def_annot) as orig_cdef) :: cdefs
        when Bindings.mem id !monomorphic_calls ->
          let tyargs = Bindings.find id !spec_tyargs in
          let specialized_fundefs =
            List.filter_map
              (fun instantiation ->
                let specialized_id = mangle_mono_id id ctx instantiation in
                if not (IdSet.mem specialized_id !specialized_calls) then (
                  specialized_calls := IdSet.add specialized_id !specialized_calls;
                  let substs =
                    List.fold_left2
                      (fun substs tyarg ty -> KBindings.add tyarg ty substs)
                      KBindings.empty tyargs instantiation
                  in
                  let body = List.map (map_instr_ctyp (subst_poly substs)) body in
                  Some (CDEF_aux (CDEF_fundef (specialized_id, heap_return, params, body), def_annot))
                )
                else None
              )
              (CTListSet.elements (Bindings.find id !monomorphic_calls))
          in
          specialize_fundefs ctx ((orig_cdef :: specialized_fundefs) @ prior) cdefs
      | cdef :: cdefs -> specialize_fundefs ctx (cdef :: prior) cdefs
      | [] -> (List.rev prior, ctx)
    in

    let cdefs, ctx = specialize_fundefs ctx [] cdefs in

    (* Now we want to remove any polymorphic functions that are
       unreachable from any monomorphic function *)
    let graph = callgraph cdefs in
    let monomorphic_roots =
      List.filter_map
        (function
          | CDEF_aux (CDEF_val (id, _, param_ctyps, ret_ctyp, _), _) ->
              if List.exists is_polymorphic param_ctyps || is_polymorphic ret_ctyp then None else Some id
          | _ -> None
          )
        cdefs
      |> IdGraphNS.of_list
    in
    let monomorphic_reachable = IdGraph.reachable monomorphic_roots IdGraphNS.empty graph in
    let unreachable_polymorphic_functions =
      IdSet.filter (fun id -> not (IdGraphNS.mem id monomorphic_reachable)) polymorphic_functions
    in
    let cdefs =
      List.filter_map
        (function
          | CDEF_aux (CDEF_fundef (id, _, _, _), _) when IdSet.mem id unreachable_polymorphic_functions -> None
          | CDEF_aux (CDEF_val (id, _, _, _, _), _) when IdSet.mem id unreachable_polymorphic_functions -> None
          | cdef -> Some cdef
          )
        cdefs
    in

    (* If we have removed all the polymorphic functions we are done, otherwise go again *)
    if IdSet.is_empty (IdSet.diff polymorphic_functions unreachable_polymorphic_functions) then (cdefs, ctx)
    else specialize_functions ~specialized_calls ctx cdefs

  let string_of_integer_interval = function
    | None -> "?"
    | Some (lower, upper) -> Big_int.to_string lower ^ ".." ^ Big_int.to_string upper

  let mangle_representation_id id ctx ctyps (argument_intervals, result_interval) =
    let representation = append_id id ("<repr:" ^ Util.string_of_list "," (mangle_string_of_ctyp ctx) ctyps ^ ">") in
    let interval_key =
      Util.string_of_list "," string_of_integer_interval (argument_intervals @ [result_interval])
      |> Digest.string |> Digest.to_hex
    in
    append_id representation ("<bounds:" ^ interval_key ^ ">")

  type integer_lifetime = Lifetime_bottom | Lifetime_range of Big_int.num * Big_int.num | Lifetime_top

  module PathInstructionMap = Map.Make (Int)

  module AggregateFieldMap = Map.Make (struct
    type t = name * id

    let compare (left_name, left_field) (right_name, right_field) =
      match Name.compare left_name right_name with 0 -> Id.compare left_field right_field | ordering -> ordering
  end)

  type integer_condition_fact = {
    comparison : Jib_semantics.comparison;
    left : cval;
    right : cval;
    comparison_when_true : bool;
    dependencies : NameSet.t;
  }

  type integer_predicate_operand = Predicate_argument of int | Predicate_literal of cval

  type integer_predicate_summary = {
    predicate_comparison : Jib_semantics.comparison;
    predicate_left : integer_predicate_operand;
    predicate_right : integer_predicate_operand;
    predicate_comparison_when_true : bool;
  }

  type path_integer_state = {
    ranges : integer_lifetime NameMap.t;
    conditions : integer_condition_fact NameMap.t;
    aggregate_fields : integer_lifetime AggregateFieldMap.t;
  }

  let integer_lifetime_equal left right =
    match (left, right) with
    | Lifetime_bottom, Lifetime_bottom | Lifetime_top, Lifetime_top -> true
    | Lifetime_range (left_lower, left_upper), Lifetime_range (right_lower, right_upper) ->
        Big_int.equal left_lower right_lower && Big_int.equal left_upper right_upper
    | _ -> false

  let join_integer_lifetime left right =
    match (left, right) with
    | Lifetime_top, _ | _, Lifetime_top -> Lifetime_top
    | Lifetime_bottom, range | range, Lifetime_bottom -> range
    | Lifetime_range (left_lower, left_upper), Lifetime_range (right_lower, right_upper) ->
        Lifetime_range (Big_int.min left_lower right_lower, Big_int.max left_upper right_upper)

  let meet_integer_lifetime left right =
    match (left, right) with
    | Lifetime_bottom, _ | _, Lifetime_bottom -> Lifetime_bottom
    | Lifetime_top, lifetime | lifetime, Lifetime_top -> lifetime
    | Lifetime_range (left_lower, left_upper), Lifetime_range (right_lower, right_upper) ->
        let lower = Big_int.max left_lower right_lower in
        let upper = Big_int.min left_upper right_upper in
        if Big_int.less_equal lower upper then Lifetime_range (lower, upper) else Lifetime_bottom

  let integer_lifetime_binary operation left right =
    match (left, right) with
    | Lifetime_bottom, _ | _, Lifetime_bottom -> Lifetime_bottom
    | Lifetime_top, _ | _, Lifetime_top -> Lifetime_top
    | Lifetime_range (left_lower, left_upper), Lifetime_range (right_lower, right_upper) ->
        operation left_lower left_upper right_lower right_upper

  let lifetime_add =
    integer_lifetime_binary (fun left_lower left_upper right_lower right_upper ->
        Lifetime_range (Big_int.add left_lower right_lower, Big_int.add left_upper right_upper)
    )

  let lifetime_sub =
    integer_lifetime_binary (fun left_lower left_upper right_lower right_upper ->
        Lifetime_range (Big_int.sub left_lower right_upper, Big_int.sub left_upper right_lower)
    )

  let lifetime_mul =
    integer_lifetime_binary (fun left_lower left_upper right_lower right_upper ->
        let products =
          [
            Big_int.mul left_lower right_lower;
            Big_int.mul left_lower right_upper;
            Big_int.mul left_upper right_lower;
            Big_int.mul left_upper right_upper;
          ]
        in
        let lower = List.fold_left Big_int.min (List.hd products) (List.tl products) in
        let upper = List.fold_left Big_int.max (List.hd products) (List.tl products) in
        Lifetime_range (lower, upper)
    )

  let truncating_div numerator denominator =
    let negative = Big_int.less numerator Big_int.zero <> Big_int.less denominator Big_int.zero in
    let absolute value = if Big_int.less value Big_int.zero then Big_int.negate value else value in
    let quotient = Big_int.div (absolute numerator) (absolute denominator) in
    if negative then Big_int.negate quotient else quotient

  let lifetime_div =
    integer_lifetime_binary (fun left_lower left_upper right_lower right_upper ->
        if Big_int.less_equal right_lower Big_int.zero && Big_int.less_equal Big_int.zero right_upper then Lifetime_top
        else (
          let quotients =
            [
              truncating_div left_lower right_lower;
              truncating_div left_lower right_upper;
              truncating_div left_upper right_lower;
              truncating_div left_upper right_upper;
            ]
          in
          let lower = List.fold_left Big_int.min (List.hd quotients) (List.tl quotients) in
          let upper = List.fold_left Big_int.max (List.hd quotients) (List.tl quotients) in
          Lifetime_range (lower, upper)
        )
    )

  let lifetime_mod =
    integer_lifetime_binary (fun left_lower left_upper right_lower right_upper ->
        if Big_int.less_equal right_lower Big_int.zero && Big_int.less_equal Big_int.zero right_upper then Lifetime_top
        else (
          let absolute value = if Big_int.less value Big_int.zero then Big_int.negate value else value in
          let maximum_divisor = Big_int.max (absolute right_lower) (absolute right_upper) in
          let magnitude = Big_int.pred maximum_divisor in
          if Big_int.less_equal Big_int.zero left_lower then
            Lifetime_range (Big_int.zero, Big_int.min left_upper magnitude)
          else if Big_int.less_equal left_upper Big_int.zero then
            Lifetime_range (Big_int.max left_lower (Big_int.negate magnitude), Big_int.zero)
          else Lifetime_range (Big_int.negate magnitude, magnitude)
        )
    )

  let lifetime_euclidean_nonnegative operation left right =
    match (left, right) with
    | Lifetime_range (left_lower, _), Lifetime_range (right_lower, _)
      when Big_int.less_equal Big_int.zero left_lower && Big_int.less Big_int.zero right_lower ->
        operation left right
    | _ -> Lifetime_top

  let ctyp_integer_lifetime ctyp =
    let unsigned_max width = Big_int.pred (Big_int.pow_int_positive 2 width) in
    match C.integer_representation_bounds ctyp with
    | Some (lower, upper) -> Lifetime_range (lower, upper)
    | None -> (
        match ctyp with
        | CT_fbits width | CT_sbits width -> Lifetime_range (Big_int.zero, unsigned_max width)
        | CT_constant value -> Lifetime_range (value, value)
        | _ -> Lifetime_top
      )

  let represented_integer_lifetime ctx = function
    | Lifetime_range (lower, upper) ->
        let represented = C.convert_typ ctx (range_typ (nconstant lower) (nconstant upper)) in
        if C.specialize_function_body_representation ~semantic:CT_lint ~represented then Some represented else None
    | Lifetime_bottom | Lifetime_top -> None

  let integer_lifetime_interval = function
    | Lifetime_range (lower, upper) -> Some (lower, upper)
    | Lifetime_bottom | Lifetime_top -> None

  let rec cval_integer_lifetime ranges = function
    | V_id (name, ctyp) -> (
        match NameMap.find_opt name ranges with
        | Some Lifetime_bottom | None -> ctyp_integer_lifetime ctyp
        | Some range -> range
      )
    | V_lit (VL_int value, _) -> Lifetime_range (value, value)
    | V_lit (VL_bits bits, ctyp) ->
        let value =
          List.fold_left
            (fun value bit ->
              Option.bind value (fun value ->
                  match bit with
                  | Sail2_values.B0 -> Some (Big_int.mul value (Big_int.of_int 2))
                  | Sail2_values.B1 -> Some (Big_int.succ (Big_int.mul value (Big_int.of_int 2)))
                  | Sail2_values.BU -> None
              )
            )
            (Some Big_int.zero) bits
        in
        Option.fold ~none:(ctyp_integer_lifetime ctyp) ~some:(fun value -> Lifetime_range (value, value)) value
    | V_call ((Slice width | Proven_slice (width, _)), [source; start]) ->
        let source = integer_lifetime_interval (cval_integer_lifetime ranges source) in
        let start = integer_lifetime_interval (cval_integer_lifetime ranges start) in
        Option.fold ~none:Lifetime_top
          ~some:(fun (lower, upper) -> Lifetime_range (lower, upper))
          (Jib_semantics.slice_result_bounds ~width ~source ~start)
    | V_call (Concat, [left; right]) ->
        let fixed_width = function CT_fbits width | CT_sbits width -> Some width | _ -> None in
        let left = integer_lifetime_interval (cval_integer_lifetime ranges left) in
        let right_bounds = integer_lifetime_interval (cval_integer_lifetime ranges right) in
        Option.fold ~none:Lifetime_top
          ~some:(fun (lower, upper) -> Lifetime_range (lower, upper))
          (Option.bind
             (fixed_width (cval_ctyp right))
             (fun right_width -> Jib_semantics.concat_result_bounds ~right_width ~left ~right:right_bounds)
          )
    | V_call (Set_slice, [base; start; inserted]) ->
        let fixed_width = function CT_fbits width | CT_sbits width -> Some width | _ -> None in
        let base_bounds = integer_lifetime_interval (cval_integer_lifetime ranges base) in
        let start_bounds = integer_lifetime_interval (cval_integer_lifetime ranges start) in
        let inserted_bounds = integer_lifetime_interval (cval_integer_lifetime ranges inserted) in
        Option.fold ~none:Lifetime_top
          ~some:(fun (lower, upper) -> Lifetime_range (lower, upper))
          (Option.bind
             (fixed_width (cval_ctyp base))
             (fun carrier_width ->
               Jib_semantics.bit_insert_result_bounds ~carrier_width ~base:base_bounds ~start:start_bounds
                 ~inserted:inserted_bounds
             )
          )
    | V_call ((Unsigned _ | Proven_narrow _ | Zero_extend _), [source]) -> cval_integer_lifetime ranges source
    | V_call (op, [left; right]) as call -> (
        let left = cval_integer_lifetime ranges left in
        let right = cval_integer_lifetime ranges right in
        let derived_bounds derive =
          Option.fold ~none:Lifetime_top
            ~some:(fun (lower, upper) -> Lifetime_range (lower, upper))
            (derive ~left:(integer_lifetime_interval left) ~right:(integer_lifetime_interval right))
        in
        match op with
        | Iadd | Proven_iadd | Widening_iadd _ | Wrapping_iadd _ -> lifetime_add left right
        | Isub | Proven_isub | Wrapping_isub _ -> lifetime_sub left right
        | Imul | Proven_imul | Widening_imul _ | Wrapping_imul _ -> lifetime_mul left right
        | Idiv | Proven_idiv | Mixed_proven_idiv _ -> lifetime_div left right
        | Imod | Proven_imod | Mixed_proven_imod _ -> lifetime_mod left right
        | Bvand -> derived_bounds Jib_semantics.bitwise_and_result_bounds
        | Bvor | Bvxor -> derived_bounds Jib_semantics.bitwise_union_result_bounds
        | _ -> ctyp_integer_lifetime (cval_ctyp call)
      )
    | V_call (Power_of_two_idiv exponent, [value]) -> (
        match cval_integer_lifetime ranges value with
        | Lifetime_range (lower, upper) ->
            let divisor = Big_int.pow_int_positive 2 exponent in
            Lifetime_range (Big_int.div lower divisor, Big_int.div upper divisor)
        | Lifetime_bottom -> Lifetime_bottom
        | Lifetime_top -> Lifetime_top
      )
    | V_call (Power_of_two_imod exponent, [value]) -> (
        match cval_integer_lifetime ranges value with
        | Lifetime_range (lower, upper) ->
            let mask = Big_int.pred (Big_int.pow_int_positive 2 exponent) in
            Lifetime_range (Big_int.zero, Big_int.min upper mask)
        | Lifetime_bottom -> Lifetime_bottom
        | Lifetime_top -> Lifetime_top
      )
    | cval -> ctyp_integer_lifetime (cval_ctyp cval)

  let integer_comparison_name ctx id =
    let name =
      match Bindings.find_opt id ctx.valspecs with
      | Some (Some external_name, _, _, _) -> external_name
      | _ -> string_of_id id
    in
    match name with
    | "eq_int" -> Some Eq
    | "neq_int" -> Some Neq
    | "lt" | "lt_int" -> Some Ilt
    | "gt" | "gt_int" -> Some Igt
    | "lteq" | "lteq_int" -> Some Ilteq
    | "gteq" | "gteq_int" -> Some Igteq
    | _ -> None

  let boolean_negation_name ctx id =
    let name =
      match Bindings.find_opt id ctx.valspecs with
      | Some (Some external_name, _, _, _) -> external_name
      | _ -> string_of_id id
    in
    String.equal name "not" || String.equal name "not_bool"

  let semantic_integer_comparison = function
    | Eq -> Some Jib_semantics.Equal
    | Neq -> Some Jib_semantics.Not_equal
    | Ilt -> Some Jib_semantics.Less_than
    | Ilteq -> Some Jib_semantics.Less_equal
    | Igt -> Some Jib_semantics.Greater_than
    | Igteq -> Some Jib_semantics.Greater_equal
    | _ -> None

  let constant_semantic_integer_comparison comparison left right =
    match (left, right) with
    | Lifetime_range (left_lower, left_upper), Lifetime_range (right_lower, right_upper) -> (
        let singleton lower upper = Big_int.equal lower upper in
        match comparison with
        | Jib_semantics.Equal ->
            if Big_int.less left_upper right_lower || Big_int.less right_upper left_lower then Some false
            else if
              singleton left_lower left_upper && singleton right_lower right_upper
              && Big_int.equal left_lower right_lower
            then Some true
            else None
        | Jib_semantics.Not_equal ->
            if Big_int.less left_upper right_lower || Big_int.less right_upper left_lower then Some true
            else if
              singleton left_lower left_upper && singleton right_lower right_upper
              && Big_int.equal left_lower right_lower
            then Some false
            else None
        | Jib_semantics.Less_than ->
            if Big_int.less left_upper right_lower then Some true
            else if Big_int.greater_equal left_lower right_upper then Some false
            else None
        | Jib_semantics.Greater_than ->
            if Big_int.greater left_lower right_upper then Some true
            else if Big_int.less_equal left_upper right_lower then Some false
            else None
        | Jib_semantics.Less_equal ->
            if Big_int.less_equal left_upper right_lower then Some true
            else if Big_int.greater left_lower right_upper then Some false
            else None
        | Jib_semantics.Greater_equal ->
            if Big_int.greater_equal left_lower right_upper then Some true
            else if Big_int.less left_upper right_lower then Some false
            else None
      )
    | Lifetime_bottom, _ | _, Lifetime_bottom | Lifetime_top, _ | _, Lifetime_top -> None

  let constant_integer_comparison comparison left right =
    Option.bind (semantic_integer_comparison comparison) (fun comparison ->
        constant_semantic_integer_comparison comparison left right
    )

  let integer_primitive_operation_lifetime primitive =
    match primitive with
    | `Add -> lifetime_add
    | `Sub -> lifetime_sub
    | `Mul -> lifetime_mul
    | `Div -> lifetime_div
    | `Mod -> lifetime_mod
    | `Ediv -> lifetime_euclidean_nonnegative lifetime_div
    | `Emod -> lifetime_euclidean_nonnegative lifetime_mod

  let integer_primitive_carrier_lifetime primitive left right =
    let result = integer_primitive_operation_lifetime primitive left right in
    join_integer_lifetime result (join_integer_lifetime left right)

  let infer_integer_lifetimes ?(call_result_lifetime = fun _ -> None) ctx function_id params actual_ctyps
      actual_intervals body =
    let ranges = ref NameMap.empty in
    let writes = ref NameMap.empty in
    let changed = ref false in
    let widening_count = ref NameMap.empty in
    let expanded_this_pass = ref NameSet.empty in
    let is_register = function Name (id, _) -> Bindings.mem id ctx.registers | _ -> false in
    let note_variable name ctyp =
      if not (is_register name) then (
        if not (NameMap.mem name !ranges) then ranges := NameMap.add name Lifetime_bottom !ranges;
        if not (NameMap.mem name !writes) then writes := NameMap.add name ctyp !writes
      )
    in
    let rec collect_instr (I_aux (instr, _)) =
      match instr with
      | I_decl (ctyp, name) | I_init (ctyp, name, _) | I_reinit (ctyp, name, _) | I_reset (ctyp, name) ->
          note_variable name ctyp
      | I_copy (CL_id (name, ctyp), _) -> note_variable name ctyp
      | I_funcall (CR_one (CL_id (name, ctyp)), _, _, _) -> note_variable name ctyp
      | I_if (_, then_instrs, else_instrs) ->
          List.iter collect_instr then_instrs;
          List.iter collect_instr else_instrs
      | I_block instrs | I_try_block instrs -> List.iter collect_instr instrs
      | _ -> ()
    in
    List.iter collect_instr body;
    List.iter2
      (fun (param, ctyp) interval ->
        note_variable param ctyp;
        let lifetime =
          match interval with
          | Some (lower, upper) -> Lifetime_range (lower, upper)
          | None -> ctyp_integer_lifetime ctyp
        in
        ranges := NameMap.add param lifetime !ranges
      )
      (List.combine params actual_ctyps) actual_intervals;
    let update name value =
      if not (is_register name) then (
        let prior =
          match NameMap.find_opt name !ranges with
          | Some prior -> prior
          | None ->
              Reporting.unreachable Parse_ast.Unknown __POS__
                (Printf.sprintf "Integer lifetime analysis encountered uncollected variable %s in %s"
                   (string_of_name name) (string_of_id function_id)
                )
        in
        let joined = join_integer_lifetime prior value in
        if not (integer_lifetime_equal prior joined) then (
          (match prior with Lifetime_bottom -> () | _ -> expanded_this_pass := NameSet.add name !expanded_this_pass);
          ranges := NameMap.add name joined !ranges;
          changed := true
        )
      )
    in
    let update_clexp clexp value = match clexp with CL_id (name, _) -> update name value | _ -> () in
    let primitive_lifetime primitive args =
      match (primitive, List.map (cval_integer_lifetime !ranges) args) with
      | `Add, [left; right] -> lifetime_add left right
      | `Sub, [left; right] -> lifetime_sub left right
      | `Mul, [left; right] -> lifetime_mul left right
      | `Div, [left; right] -> lifetime_div left right
      | `Mod, [left; right] -> lifetime_mod left right
      | `Ediv, [left; right] -> lifetime_euclidean_nonnegative lifetime_div left right
      | `Emod, [left; right] -> lifetime_euclidean_nonnegative lifetime_mod left right
      | _ -> Lifetime_top
    in
    let assigned_integer_lifetime destination_ctyp value =
      match (destination_ctyp, value) with
      | CT_lint, V_lit (VL_string literal, CT_string) -> (
          (* Large mathematical-integer literals are lowered through a decimal
             string because the ordinary C runtime initializes [sail_int]
             values with GMP.  Recover the source literal here so lifetime
             specialization can select a proved fixed-width representation
             before the backend emits that runtime initialization. *)
          match Sail_lib.int_of_string_opt literal with
          | Some value -> Lifetime_range (value, value)
          | None -> Lifetime_top
        )
      | _ -> cval_integer_lifetime !ranges value
    in
    let rec analyze_instr (I_aux (instr, _)) =
      match instr with
      | I_init (ctyp, name, Init_cval value) | I_reinit (ctyp, name, value) ->
          let lifetime = assigned_integer_lifetime ctyp value in
          update name lifetime
      | I_copy (clexp, value) ->
          let lifetime = assigned_integer_lifetime (clexp_ctyp clexp) value in
          update_clexp clexp lifetime
      | I_funcall (CR_one clexp, Call ((_, result_interval), _), (id, _), args) -> (
          match integer_primitive_name ctx id with
          | Some primitive -> update_clexp clexp (primitive_lifetime primitive args)
          | None ->
              let annotated =
                match result_interval with
                | Some (lower, upper) -> Lifetime_range (lower, upper)
                | None -> ctyp_integer_lifetime (clexp_ctyp clexp)
              in
              let lifetime =
                match call_result_lifetime id with
                | Some summary -> meet_integer_lifetime annotated summary
                | None -> annotated
              in
              update_clexp clexp lifetime
        )
      | I_funcall (CR_one clexp, _, _, _) -> update_clexp clexp (ctyp_integer_lifetime (clexp_ctyp clexp))
      | I_if (_, then_instrs, else_instrs) ->
          List.iter analyze_instr then_instrs;
          List.iter analyze_instr else_instrs
      | I_block instrs | I_try_block instrs -> List.iter analyze_instr instrs
      | _ -> ()
    in
    changed := true;
    let pass = ref 0 in
    while !changed do
      incr pass;
      changed := false;
      expanded_this_pass := NameSet.empty;
      List.iter analyze_instr body;
      (* A loop-carried mathematical integer without a source-level ceiling can
         otherwise grow by one arithmetic step on every whole-function pass.
         That is neither a proof of a finite native representation nor a useful
         fixed point.  Widen after a few genuine cross-pass expansions; values
         whose dependent Sail types or call bounds provide a ceiling converge
         before this point, while unresolved recurrences conservatively remain
         [sail_int]. *)
      NameSet.iter
        (fun name ->
          let count = Option.value ~default:0 (NameMap.find_opt name !widening_count) + 1 in
          widening_count := NameMap.add name count !widening_count;
          if count >= 4 then ranges := NameMap.add name Lifetime_top !ranges
        )
        !expanded_this_pass;
      if !opt_debug_function_representations && (!pass <= 10 || !pass mod 100 = 0) then
        Printf.eprintf
          "C representation specialization: lifetime function=%s pass=%d values=%d expanded=%d changed=%b\n%!"
          (string_of_id function_id) !pass (NameMap.cardinal !ranges) (NameSet.cardinal !expanded_this_pass) !changed
    done;
    (!ranges, !writes)

  (* Whole-lifetime ranges above answer which representation can safely store a
     value everywhere it is live.  This second analysis answers a different
     question: what is known immediately before a particular instruction?
     Keeping the two facts separate lets a guard specialize arithmetic and
     call-graph edges in one arm without incorrectly narrowing the variable's
     function-wide storage. *)
  let infer_path_integer_lifetimes ?(call_result_lifetime = fun _ -> None) ?(call_predicate_fact = fun _ _ -> None) ctx
      function_id global_ranges body =
    let paths = ref PathInstructionMap.empty in
    let decisions = ref PathInstructionMap.empty in
    let storage_ranges = ref NameMap.empty in
    let collect_storage = ref false in
    let note_storage name lifetime =
      if !collect_storage then (
        let lifetime =
          match NameMap.find_opt name !storage_ranges with
          | Some prior -> join_integer_lifetime prior lifetime
          | None -> lifetime
        in
        storage_ranges := NameMap.add name lifetime !storage_ranges
      )
    in
    let path_cval_integer_lifetime state = function
      | V_field (V_id (name, _), field, ctyp) ->
          Option.value ~default:(ctyp_integer_lifetime ctyp)
            (AggregateFieldMap.find_opt (name, field) state.aggregate_fields)
      | value -> cval_integer_lifetime state.ranges value
    in
    let assigned_integer_lifetime state destination_ctyp value =
      match (destination_ctyp, value) with
      | CT_lint, V_lit (VL_string literal, CT_string) -> (
          match Sail_lib.int_of_string_opt literal with
          | Some value -> Lifetime_range (value, value)
          | None -> Lifetime_top
        )
      | _ -> path_cval_integer_lifetime state value
    in
    let primitive_lifetime state primitive args =
      match (primitive, List.map (path_cval_integer_lifetime state) args) with
      | `Add, [left; right] -> lifetime_add left right
      | `Sub, [left; right] -> lifetime_sub left right
      | `Mul, [left; right] -> lifetime_mul left right
      | `Div, [left; right] -> lifetime_div left right
      | `Mod, [left; right] -> lifetime_mod left right
      | `Ediv, [left; right] -> lifetime_euclidean_nonnegative lifetime_div left right
      | `Emod, [left; right] -> lifetime_euclidean_nonnegative lifetime_mod left right
      | _ -> Lifetime_top
    in
    let invalidate_conditions name state =
      {
        state with
        conditions =
          NameMap.filter
            (fun condition_name fact ->
              Name.compare condition_name name <> 0 && not (NameSet.mem name fact.dependencies)
            )
            state.conditions;
      }
    in
    let forget_aggregate name state =
      {
        state with
        aggregate_fields =
          AggregateFieldMap.filter
            (fun (aggregate_name, _) _ -> Name.compare aggregate_name name <> 0)
            state.aggregate_fields;
      }
    in
    let invalidate name state = forget_aggregate name (invalidate_conditions name state) in
    let write name lifetime state =
      let state = invalidate name state in
      note_storage name lifetime;
      { state with ranges = NameMap.add name lifetime state.ranges }
    in
    let write_aggregate_field name field lifetime state =
      let state = invalidate_conditions name state in
      { state with aggregate_fields = AggregateFieldMap.add (name, field) lifetime state.aggregate_fields }
    in
    let rec invalidate_clexp clexp state =
      match clexp with
      | CL_id (name, _) -> invalidate name state
      | CL_rmw (_, write_name, _) -> invalidate write_name state
      | CL_field (base, _, _) | CL_tuple (base, _) | CL_addr base -> invalidate_clexp base state
      | CL_void _ -> state
    in
    let reset_clexp clexp state =
      match clexp with
      | CL_id (name, ctyp) | CL_rmw (_, name, ctyp) ->
          let lifetime = Option.value ~default:(ctyp_integer_lifetime ctyp) (NameMap.find_opt name global_ranges) in
          write name lifetime state
      | CL_field _ | CL_tuple _ | CL_addr _ | CL_void _ -> invalidate_clexp clexp state
    in
    let reset_creturn creturn state =
      match creturn with
      | CR_one clexp -> reset_clexp clexp state
      | CR_multi clexps -> List.fold_left (fun state clexp -> reset_clexp clexp state) state clexps
    in
    let write_clexp clexp lifetime state =
      match clexp with
      | CL_id (name, _) -> write name lifetime state
      | CL_field (CL_id (name, _), field, _) -> write_aggregate_field name field lifetime state
      | _ -> invalidate_clexp clexp state
    in
    let aggregate_fields_from_value state = function
      | V_id (source, _) ->
          Some
            (AggregateFieldMap.fold
               (fun (aggregate_name, field) lifetime fields ->
                 if Name.compare aggregate_name source = 0 then (field, lifetime) :: fields else fields
               )
               state.aggregate_fields []
            )
      | V_struct (fields, _) ->
          Some (List.map (fun (field, value) -> (field, path_cval_integer_lifetime state value)) fields)
      | _ -> None
    in
    let install_aggregate_fields destination fields state =
      match (destination, fields) with
      | CL_id (name, _), Some fields ->
          List.fold_left (fun state (field, lifetime) -> write_aggregate_field name field lifetime state) state fields
      | _ -> state
    in
    let rec cval_dependencies = function
      | V_id (name, _) -> NameSet.singleton name
      | V_lit _ | V_member _ -> NameSet.empty
      | V_field (value, _, _) | V_tuple_member (value, _, _) | V_ctor_kind (value, _) | V_ctor_unwrap (value, _, _) ->
          cval_dependencies value
      | V_call (_, values) | V_tuple values ->
          List.fold_left
            (fun dependencies value -> NameSet.union dependencies (cval_dependencies value))
            NameSet.empty values
      | V_struct (fields, _) ->
          List.fold_left
            (fun dependencies (_, value) -> NameSet.union dependencies (cval_dependencies value))
            NameSet.empty fields
    in
    let condition_operand state value =
      match (value, integer_lifetime_interval (path_cval_integer_lifetime state value)) with
      | V_id (_, ctyp), Some (lower, upper) when Big_int.equal lower upper ->
          (* Comparison lowering can introduce a scoped temporary for a
             negative literal.  Snapshot singleton operands into the fact so
             clearing that temporary does not discard a still-valid relation
             between the condition result and the variables it constrains. *)
          V_lit (VL_int lower, ctyp)
      | _ -> value
    in
    let remembered_condition state ?(comparison_when_true = true) comparison left right =
      let left = condition_operand state left in
      let right = condition_operand state right in
      Some
        {
          comparison;
          left;
          right;
          comparison_when_true;
          dependencies = NameSet.union (cval_dependencies left) (cval_dependencies right);
        }
    in
    let condition_fact state ?(comparison_when_true = true) comparison left right =
      Option.bind (semantic_integer_comparison comparison) (fun comparison ->
          remembered_condition state ~comparison_when_true comparison left right
      )
    in
    let rec condition_from_cval state = function
      | V_id (name, _) -> NameMap.find_opt name state.conditions
      | V_call (Bnot, [condition]) ->
          Option.map
            (fun fact -> { fact with comparison_when_true = not fact.comparison_when_true })
            (condition_from_cval state condition)
      | V_call (comparison, [left; right]) -> condition_fact state comparison left right
      | _ -> None
    and condition_from_call state id args =
      match (boolean_negation_name ctx id, args) with
      | true, [condition] ->
          Option.map
            (fun fact -> { fact with comparison_when_true = not fact.comparison_when_true })
            (condition_from_cval state condition)
      | _ -> (
          match (integer_comparison_name ctx id, args) with
          | Some comparison, [left; right] -> condition_fact state comparison left right
          | _ -> (
              match call_predicate_fact id args with
              | Some (comparison, left, right, comparison_when_true) ->
                  remembered_condition state ~comparison_when_true comparison left right
              | None -> None
            )
        )
    in
    let condition_fact_value state fact =
      Option.map
        (fun comparison_value -> if fact.comparison_when_true then comparison_value else not comparison_value)
        (constant_semantic_integer_comparison fact.comparison
           (path_cval_integer_lifetime state fact.left)
           (path_cval_integer_lifetime state fact.right)
        )
    in
    let rec constant_condition state = function
      | V_lit (VL_bool value, _) -> Some value
      | V_call (Bnot, [condition]) -> Option.map not (constant_condition state condition)
      | V_id (name, _) -> Option.bind (NameMap.find_opt name state.conditions) (condition_fact_value state)
      | condition -> Option.bind (condition_from_cval state condition) (condition_fact_value state)
    in
    let remember_condition destination fact state =
      match (destination, fact) with
      | CL_id (name, _), Some fact -> { state with conditions = NameMap.add name fact state.conditions }
      | _ -> state
    in
    let refine_cval ranges cval lifetime =
      match cval with V_id (name, _) -> NameMap.add name lifetime ranges | _ -> ranges
    in
    let refine fact truth state =
      let truth = if fact.comparison_when_true then truth else not truth in
      match
        ( integer_lifetime_interval (path_cval_integer_lifetime state fact.left),
          integer_lifetime_interval (path_cval_integer_lifetime state fact.right)
        )
      with
      | Some left, Some right -> (
          match Jib_semantics.refine_comparison_bounds fact.comparison ~truth ~left ~right with
          | Some (left, right) ->
              let left_lower, left_upper = left in
              let right_lower, right_upper = right in
              if !opt_debug_function_representations then
                Printf.eprintf
                  "C representation specialization: path-refinement function=%s truth=%b left=%s right=%s\n%!"
                  (string_of_id function_id) truth
                  (string_of_integer_interval (Some (left_lower, left_upper)))
                  (string_of_integer_interval (Some (right_lower, right_upper)));
              {
                state with
                ranges =
                  refine_cval
                    (refine_cval state.ranges fact.left (Lifetime_range (left_lower, left_upper)))
                    fact.right
                    (Lifetime_range (right_lower, right_upper));
              }
          | None -> state
        )
      | _ -> state
    in
    let rec refine_condition condition truth state =
      match condition with
      | V_call (Bnot, [condition]) -> refine_condition condition (not truth) state
      | V_id (name, _) ->
          Option.fold ~none:state ~some:(fun fact -> refine fact truth state) (NameMap.find_opt name state.conditions)
      | condition ->
          Option.fold ~none:state ~some:(fun fact -> refine fact truth state) (condition_from_cval state condition)
    in
    let join_ranges left right =
      NameMap.merge
        (fun _ left right ->
          match (left, right) with
          | Some left, Some right -> Some (join_integer_lifetime left right)
          | Some lifetime, None | None, Some lifetime -> Some lifetime
          | None, None -> None
        )
        left right
    in
    let join_conditions left right =
      NameMap.merge
        (fun _ left right -> match (left, right) with Some left, Some right when left = right -> Some left | _ -> None)
        left right
    in
    let join_aggregate_fields left right =
      AggregateFieldMap.merge
        (fun _ left right ->
          match (left, right) with
          | Some left, Some right -> Some (join_integer_lifetime left right)
          | Some _, None | None, Some _ | None, None -> None
        )
        left right
    in
    let join_states left right =
      {
        ranges = join_ranges left.ranges right.ranges;
        conditions = join_conditions left.conditions right.conditions;
        aggregate_fields = join_aggregate_fields left.aggregate_fields right.aggregate_fields;
      }
    in
    let state_equal left right =
      NameMap.equal integer_lifetime_equal left.ranges right.ranges
      && NameMap.equal ( = ) left.conditions right.conditions
      && AggregateFieldMap.equal integer_lifetime_equal left.aggregate_fields right.aggregate_fields
    in
    let transfer_instr state (I_aux (instr, _)) =
      match instr with
      | I_init (ctyp, name, Init_cval value) | I_reinit (ctyp, name, value) ->
          let aggregate_fields = aggregate_fields_from_value state value in
          let state = write name (assigned_integer_lifetime state ctyp value) state in
          install_aggregate_fields (CL_id (name, ctyp)) aggregate_fields state
      | I_init (_, name, _) | I_reset (_, name) ->
          let lifetime = Option.value ~default:Lifetime_top (NameMap.find_opt name global_ranges) in
          write name lifetime state
      | I_copy (clexp, value) ->
          let aggregate_fields = aggregate_fields_from_value state value in
          let lifetime = assigned_integer_lifetime state (clexp_ctyp clexp) value in
          let state = write_clexp clexp lifetime state in
          let state = install_aggregate_fields clexp aggregate_fields state in
          remember_condition clexp (condition_from_cval state value) state
      | I_funcall (CR_one clexp, Call ((_, result_interval), _), (id, _), args) ->
          let lifetime =
            match integer_primitive_name ctx id with
            | Some primitive -> primitive_lifetime state primitive args
            | None -> (
                let annotated =
                  match result_interval with
                  | Some (lower, upper) -> Lifetime_range (lower, upper)
                  | None -> ctyp_integer_lifetime (clexp_ctyp clexp)
                in
                match call_result_lifetime id with
                | Some summary -> meet_integer_lifetime annotated summary
                | None -> annotated
              )
          in
          let state = write_clexp clexp lifetime state in
          remember_condition clexp (condition_from_call state id args) state
      | I_funcall (CR_one clexp, _, _, _) -> write_clexp clexp (ctyp_integer_lifetime (clexp_ctyp clexp)) state
      | I_funcall (creturn, _, _, _) -> reset_creturn creturn state
      | I_clear (_, name) -> invalidate name state
      | _ -> state
    in
    (* Build a small CFG over the original JIB instructions rather than using
       [flatten_instrs], which alpha-renames scoped locals.  Instruction
       numbers and names therefore remain exactly those consumed by the later
       representation-rewrite pass. *)
    let nodes = Hashtbl.create 128 in
    let edges = Hashtbl.create 128 in
    let labels = Hashtbl.create 32 in
    let rec collect_labels (I_aux (instr, (instruction, _))) =
      (match instr with I_label label -> Hashtbl.replace labels label instruction | _ -> ());
      match instr with
      | I_if (_, then_instrs, else_instrs) ->
          List.iter collect_labels then_instrs;
          List.iter collect_labels else_instrs
      | I_block instrs | I_try_block instrs -> List.iter collect_labels instrs
      | _ -> ()
    in
    List.iter collect_labels body;
    let add_edge instruction condition target =
      match target with
      | Some target ->
          let prior = Option.value ~default:[] (Hashtbl.find_opt edges instruction) in
          Hashtbl.replace edges instruction ((target, condition) :: prior)
      | None -> ()
    in
    let label_target label = Hashtbl.find_opt labels label in
    let rec build_sequence instrs continuation =
      match instrs with
      | [] -> continuation
      | instr :: instrs ->
          let continuation = build_sequence instrs continuation in
          Some (build_instr instr continuation)
    and build_instr (I_aux (instr, (instruction, _)) as whole_instr) continuation =
      Hashtbl.replace nodes instruction whole_instr;
      ( match instr with
      | I_if (condition, then_instrs, else_instrs) ->
          let then_entry = build_sequence then_instrs continuation in
          let else_entry = build_sequence else_instrs continuation in
          add_edge instruction (Some (condition, true)) then_entry;
          add_edge instruction (Some (condition, false)) else_entry
      | I_block instrs -> add_edge instruction None (build_sequence instrs continuation)
      | I_try_block instrs ->
          (* An exception may leave a try block before its normal tail. *)
          add_edge instruction None (build_sequence instrs continuation);
          add_edge instruction None continuation
      | I_goto label -> add_edge instruction None (label_target label)
      | I_jump (condition, label) ->
          add_edge instruction (Some (condition, true)) (label_target label);
          add_edge instruction (Some (condition, false)) continuation
      | I_end _ | I_exit _ | I_undefined _ -> ()
      | _ -> add_edge instruction None continuation
      );
      instruction
    in
    let entry = build_sequence body None in
    let input_states = Hashtbl.create (Hashtbl.length nodes) in
    let worklist = Queue.create () in
    let widening_counts = Hashtbl.create 64 in
    let widen target old_state joined_state =
      let ranges =
        NameMap.mapi
          (fun name joined ->
            match NameMap.find_opt name old_state.ranges with
            | Some old when not (integer_lifetime_equal old joined) ->
                let key = (target, name) in
                let count = Option.value ~default:0 (Hashtbl.find_opt widening_counts key) + 1 in
                Hashtbl.replace widening_counts key count;
                if count >= 4 then Option.value ~default:Lifetime_top (NameMap.find_opt name global_ranges) else joined
            | _ -> joined
          )
          joined_state.ranges
      in
      { joined_state with ranges }
    in
    let enqueue target incoming =
      match Hashtbl.find_opt input_states target with
      | None ->
          Hashtbl.replace input_states target incoming;
          Queue.add target worklist
      | Some old_state ->
          let joined_state = widen target old_state (join_states old_state incoming) in
          if not (state_equal old_state joined_state) then (
            Hashtbl.replace input_states target joined_state;
            Queue.add target worklist
          )
    in
    Option.iter
      (fun entry ->
        enqueue entry { ranges = global_ranges; conditions = NameMap.empty; aggregate_fields = AggregateFieldMap.empty }
      )
      entry;
    while not (Queue.is_empty worklist) do
      let instruction = Queue.take worklist in
      let input = Hashtbl.find input_states instruction in
      let output = transfer_instr input (Hashtbl.find nodes instruction) in
      List.iter
        (fun (target, condition) ->
          match condition with
          | Some (condition, truth) -> (
              match constant_condition output condition with
              | Some value when value <> truth -> ()
              | Some _ | None -> enqueue target (refine_condition condition truth output)
            )
          | None -> enqueue target output
        )
        (Option.value ~default:[] (Hashtbl.find_opt edges instruction))
    done;
    (* Storage bounds are accumulated only after the input fixed point.  This
       avoids retaining transient ranges from intermediate loop iterations. *)
    collect_storage := true;
    Hashtbl.iter
      (fun instruction state ->
        paths := PathInstructionMap.add instruction state.ranges !paths;
        let whole_instr = Hashtbl.find nodes instruction in
        ( match whole_instr with
        | I_aux ((I_if (condition, _, _) | I_jump (condition, _)), _) ->
            Option.iter
              (fun decision -> decisions := PathInstructionMap.add instruction decision !decisions)
              (constant_condition state condition)
        | _ -> ()
        );
        ignore (transfer_instr state whole_instr)
      )
      input_states;
    (!paths, !storage_ranges, !decisions)

  let path_sensitive_storage_ranges global_ranges path_storage_ranges =
    NameMap.union (fun _ path_lifetime _ -> Some path_lifetime) path_storage_ranges global_ranges

  let instruction_lifetime_ranges global_ranges path_ranges (I_aux (_, (instruction, _))) =
    Option.value ~default:global_ranges (PathInstructionMap.find_opt instruction path_ranges)

  let map_instr_with_lifetime_ranges global_ranges path_ranges f =
    map_instr (fun instr -> f (instruction_lifetime_ranges global_ranges path_ranges instr) instr)

  let proven_fixed_integer_conversion represented interval value =
    let source_has_integer_representation =
      Option.is_some (C.integer_representation_bounds (cval_ctyp value))
      || match cval_ctyp value with CT_fbits _ -> true | _ -> false
    in
    match (C.integer_representation_bounds represented, interval) with
    | Some (represented_lower, represented_upper), Some (lower, upper)
      when source_has_integer_representation
           && Big_int.less_equal represented_lower lower
           && Big_int.less_equal upper represented_upper ->
        Some (V_call (Proven_narrow represented, [value]))
    | _ -> None

  let prune_proved_unreachable path_ranges path_decisions body =
    let rec rewrite instrs =
      List.filter_map
        (fun (I_aux (instr, ((instruction, _) as aux)) as original) ->
          if not (PathInstructionMap.mem instruction path_ranges) then None
          else (
            match instr with
            | I_if (condition, then_instrs, else_instrs) -> (
                match PathInstructionMap.find_opt instruction path_decisions with
                | Some true -> Some (I_aux (I_block (rewrite then_instrs), aux))
                | Some false -> Some (I_aux (I_block (rewrite else_instrs), aux))
                | None -> Some (I_aux (I_if (condition, rewrite then_instrs, rewrite else_instrs), aux))
              )
            | I_jump (_, label) -> (
                match PathInstructionMap.find_opt instruction path_decisions with
                | Some true -> Some (I_aux (I_goto label, aux))
                | Some false -> Some (I_aux (I_block [], aux))
                | None -> Some original
              )
            | I_block instrs -> Some (I_aux (I_block (rewrite instrs), aux))
            | I_try_block instrs -> Some (I_aux (I_try_block (rewrite instrs), aux))
            | _ -> Some original
          )
        )
        instrs
    in
    rewrite body

  class specialize_parameter_representations replacements semantic_ret_ctyp represented_ret_ctyp =
    let representation_for = function
      | Return _ -> Some represented_ret_ctyp | name -> NameMap.find_opt name replacements
    in
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren

      method! vcval =
        function
        | V_id (name, _) as cval -> (
            match representation_for name with
            | Some represented -> ChangeTo (V_id (name, represented))
            | None -> ChangeTo cval
          )
        | _ -> DoChildren

      method! vclexp =
        function
        | CL_id (name, _) as clexp -> (
            match representation_for name with
            | Some represented -> ChangeTo (CL_id (name, represented))
            | None -> ChangeTo clexp
          )
        | CL_rmw (read, write, _) as clexp -> (
            match (representation_for read, representation_for write) with
            | Some read_ctyp, Some write_ctyp when not (ctyp_equal read_ctyp write_ctyp) ->
                Reporting.unreachable Parse_ast.Unknown __POS__
                  "Read-modify-write names have different specialized representations"
            | Some represented, _ | _, Some represented -> ChangeTo (CL_rmw (read, write, represented))
            | None, None -> ChangeTo clexp
          )
        | _ -> DoChildren

      method! vinstr =
        function
        | I_aux (I_undefined ctyp, aux) when ctyp_equal ctyp semantic_ret_ctyp ->
            ChangeTo (I_aux (I_undefined represented_ret_ctyp, aux))
        | I_aux (I_decl (_, name), aux) as instr -> (
            match representation_for name with
            | Some represented -> ChangeTo (I_aux (I_decl (represented, name), aux))
            | None -> ChangeTo instr
          )
        | I_aux (I_init (_, name, init), aux) as instr -> (
            match representation_for name with
            | Some represented -> change_do_children (I_aux (I_init (represented, name, init), aux))
            | None -> change_do_children instr
          )
        | I_aux (I_clear (_, name), aux) as instr -> (
            match representation_for name with
            | Some represented -> ChangeTo (I_aux (I_clear (represented, name), aux))
            | None -> ChangeTo instr
          )
        | I_aux (I_reset (_, name), aux) as instr -> (
            match representation_for name with
            | Some represented -> ChangeTo (I_aux (I_reset (represented, name), aux))
            | None -> ChangeTo instr
          )
        | I_aux (I_reinit (_, name, cval), aux) as instr -> (
            match representation_for name with
            | Some represented -> change_do_children (I_aux (I_reinit (represented, name, cval), aux))
            | None -> change_do_children instr
          )
        | _ -> DoChildren
    end

  (* Keep native subtype representations across ordinary local function
     boundaries by cloning only the signatures that are actually called.  A
     clone is derived from the canonical JIB body, and calls discovered in the
     clone enqueue further clones, so representation specialization propagates
     transitively without duplicating Sail source. *)
  let specialize_function_representations ctx cdefs =
    (* Discover semantic wrapping-arithmetic webs before any local or
       function representation is specialized.  The source idiom

         tmod_nat(left * right, 2^N)

       permits an N-bit wrapping multiply even though the mathematical product
       itself may require up to 2N bits.  That fact must not be reconstructed
       from the eventual C types: specialization can widen the product and can
       independently narrow either operand at a call boundary.

       JIB instruction annotations have stable identities and are preserved
       when a canonical body is cloned.  Record the proved reduction root in a
       side table, then consult it after each clone has acquired concrete
       representations.  A clone whose carrier/operand representations do not
       support the native operation keeps the original exact multiply/modulo
       web and follows the ordinary lowering path.

       This is intentionally a small first instance of a more general
       semantic-web mechanism: discovery depends on semantic call bounds and
       source operations, while selection depends on target representations. *)
    let same_name left right = Name.compare left right = 0 in
    let is_named names id = List.exists (String.equal (string_of_id id)) names in
    let arithmetic_primitive id =
      match integer_primitive_name ctx id with
      | Some `Add -> Some Jib_semantics.Add
      | Some `Sub -> Some Jib_semantics.Subtract
      | Some `Mul -> Some Jib_semantics.Multiply
      | _ -> None
    in
    let arithmetic_primitive_of_op = function
      | Iadd | Proven_iadd | Widening_iadd _ -> Some Jib_semantics.Add
      | Isub | Proven_isub -> Some Jib_semantics.Subtract
      | Imul | Proven_imul | Widening_imul _ -> Some Jib_semantics.Multiply
      | _ -> None
    in
    let truncating_reduction_primitive id = is_named ["tmod_int"; "tmod_nat"; "__sail_proven_native_mod"] id in
    let reduction_primitive id =
      if truncating_reduction_primitive id then Some Jib_semantics.Truncating
      else if is_named ["emod_int"; "emod_positive"] id then Some Jib_semantics.Euclidean
      else None
    in
    let reduction_may_observe_low_bits operation reduction =
      match (operation, reduction) with
      | (Jib_semantics.Add | Jib_semantics.Multiply), (Jib_semantics.Truncating | Jib_semantics.Euclidean) -> true
      | Jib_semantics.Subtract, Jib_semantics.Euclidean -> true
      | Jib_semantics.Subtract, Jib_semantics.Truncating -> true
    in
    let reduction_observes_low_bits operation reduction proofs =
      match (operation, reduction) with
      | (Jib_semantics.Add | Jib_semantics.Multiply), (Jib_semantics.Truncating | Jib_semantics.Euclidean) -> true
      | Jib_semantics.Subtract, Jib_semantics.Euclidean -> true
      | Jib_semantics.Subtract, Jib_semantics.Truncating ->
          Jib_semantics.has_argument_le ~left:1 ~right:0 proofs || Jib_semantics.has_result_nonnegative proofs
    in
    let converted_arithmetic result_name = function
      | [
          I_aux ((I_decl (CT_lint, left_int) | I_reset (CT_lint, left_int)), _);
          I_aux (I_copy (CL_id (left_copy, CT_lint), left), _);
          I_aux ((I_decl (CT_lint, right_int) | I_reset (CT_lint, right_int)), _);
          I_aux (I_copy (CL_id (right_copy, CT_lint), right), _);
          I_aux
            ( I_funcall
                ( CR_one (CL_id (product_result, CT_lint)),
                  Call (bounds, semantic_proofs),
                  (arithmetic, _),
                  [V_id (left_arg, CT_lint); V_id (right_arg, CT_lint)]
                ),
              _
            );
        ]
        when same_name left_int left_copy && same_name left_int left_arg && same_name right_int right_copy
             && same_name right_int right_arg && same_name result_name product_result ->
          Option.map
            (fun operation -> (operation, left, right, bounds, semantic_proofs))
            (arithmetic_primitive arithmetic)
      | [
          I_aux ((I_decl (CT_lint, left_int) | I_reset (CT_lint, left_int)), _);
          I_aux (I_copy (CL_id (left_copy, CT_lint), left), _);
          I_aux ((I_decl (CT_lint, right_int) | I_reset (CT_lint, right_int)), _);
          I_aux (I_copy (CL_id (right_copy, CT_lint), right), _);
          I_aux
            ( I_funcall
                ( CR_one (CL_id (product_result, CT_lint)),
                  Call (bounds, semantic_proofs),
                  (arithmetic, _),
                  [V_id (left_arg, CT_lint); V_id (right_arg, CT_lint)]
                ),
              _
            );
          I_aux (I_clear (CT_lint, right_clear), _);
          I_aux (I_clear (CT_lint, left_clear), _);
        ]
        when same_name left_int left_copy && same_name left_int left_arg && same_name left_int left_clear
             && same_name right_int right_copy && same_name right_int right_arg && same_name right_int right_clear
             && same_name result_name product_result ->
          Option.map
            (fun operation -> (operation, left, right, bounds, semantic_proofs))
            (arithmetic_primitive arithmetic)
      | _ -> None
    in
    let reduced_destination product_name modulus_name = function
      | [
          I_aux ((I_decl (CT_lint, remainder) | I_reset (CT_lint, remainder)), _);
          I_aux
            ( I_funcall
                ( CR_one (CL_id (remainder_result, CT_lint)),
                  Call (reduction_bounds, _),
                  (modulo, _),
                  [V_id (product_arg, CT_lint); V_id (modulus_arg, CT_lint)]
                ),
              _
            );
          I_aux (I_copy (destination, V_id (remainder_copy, CT_lint)), copy_aux);
        ]
        when same_name remainder remainder_result && same_name remainder remainder_copy
             && same_name product_name product_arg && same_name modulus_name modulus_arg -> (
          match reduction_primitive modulo with
          | Some reduction -> Some (reduction, destination, reduction_bounds, copy_aux)
          | None -> None
        )
      | [
          I_aux ((I_decl (CT_lint, remainder) | I_reset (CT_lint, remainder)), _);
          I_aux
            ( I_funcall
                ( CR_one (CL_id (remainder_result, CT_lint)),
                  Call (reduction_bounds, _),
                  (modulo, _),
                  [V_id (product_arg, CT_lint); V_id (modulus_arg, CT_lint)]
                ),
              _
            );
          I_aux (I_copy (destination, V_id (remainder_copy, CT_lint)), copy_aux);
          I_aux (I_clear (CT_lint, remainder_clear), _);
        ]
        when same_name remainder remainder_result && same_name remainder remainder_copy
             && same_name remainder remainder_clear && same_name product_name product_arg
             && same_name modulus_name modulus_arg -> (
          match reduction_primitive modulo with
          | Some reduction -> Some (reduction, destination, reduction_bounds, copy_aux)
          | None -> None
        )
      | _ -> None
    in
    let modulus_initializer = function
      | I_aux (I_init (CT_lint, modulus, Init_cval (V_lit (VL_int literal, _))), _) -> Some (modulus, literal)
      | I_aux (I_reinit (CT_lint, modulus, V_lit (VL_int literal, _)), _) -> Some (modulus, literal)
      | I_aux (I_init (CT_lint, modulus, Init_cval (V_lit (VL_string literal, CT_string))), _)
      | I_aux (I_reinit (CT_lint, modulus, V_lit (VL_string literal, CT_string)), _) ->
          Option.map (fun literal -> (modulus, literal)) (Sail_lib.int_of_string_opt literal)
      | _ -> None
    in
    let integer_literal = function
      | V_lit (VL_int literal, _) -> Some literal
      | V_lit (VL_string literal, CT_string) -> Sail_lib.int_of_string_opt literal
      | _ -> None
    in
    let widening_native_modular_arithmetic = function
      | [
          I_aux ((I_decl (product_ctyp, product) | I_reset (product_ctyp, product)), _);
          I_aux
            ( I_block
                [
                  I_aux (I_init (exact_ctyp, exact, Init_cval (V_call (arithmetic_op, [left; right]))), _);
                  I_aux (I_copy (CL_id (product_copy, product_copy_ctyp), V_id (exact_copy, exact_copy_ctyp)), _);
                  I_aux (I_clear (exact_clear_ctyp, exact_clear), _);
                ],
              _
            );
          I_aux
            ( I_copy
                (destination, V_call ((Imod | Proven_imod), [V_id (product_arg, product_arg_ctyp); modulus_literal])),
              reduction_aux
            );
          I_aux (I_clear (product_clear_ctyp, product_clear), _);
        ]
        when same_name exact exact_copy && same_name exact exact_clear && ctyp_equal exact_ctyp exact_copy_ctyp
             && ctyp_equal exact_ctyp exact_clear_ctyp && same_name product product_copy
             && same_name product product_arg && same_name product product_clear
             && ctyp_equal product_ctyp product_copy_ctyp
             && ctyp_equal product_ctyp product_arg_ctyp
             && ctyp_equal product_ctyp product_clear_ctyp ->
          Option.bind (arithmetic_primitive_of_op arithmetic_op) (fun operation ->
              Option.map
                (fun modulus ->
                  let bounds =
                    ( [
                        C.integer_representation_bounds (cval_ctyp left);
                        C.integer_representation_bounds (cval_ctyp right);
                      ],
                      C.integer_representation_bounds exact_ctyp
                    )
                  in
                  let reduction_bounds =
                    ( [
                        C.integer_representation_bounds product_ctyp;
                        C.integer_representation_bounds (cval_ctyp modulus_literal);
                      ],
                      C.integer_representation_bounds (clexp_ctyp destination)
                    )
                  in
                  ( operation,
                    Jib_semantics.Truncating,
                    modulus,
                    bounds,
                    [],
                    reduction_bounds,
                    destination,
                    left,
                    right,
                    reduction_aux
                  )
                )
                (integer_literal modulus_literal)
          )
      | [
          I_aux ((I_decl (product_ctyp, product) | I_reset (product_ctyp, product)), _);
          I_aux
            ( I_block
                [
                  I_aux (I_init (exact_ctyp, exact, Init_cval (V_call (arithmetic_op, [left; right]))), _);
                  I_aux (I_copy (CL_id (product_copy, product_copy_ctyp), V_id (exact_copy, exact_copy_ctyp)), _);
                  I_aux (I_clear (exact_clear_ctyp, exact_clear), _);
                ],
              _
            );
          I_aux
            ( I_funcall
                ( CR_one destination,
                  Call (reduction_bounds, _),
                  (modulo, _),
                  [V_id (product_arg, product_arg_ctyp); modulus_literal]
                ),
              reduction_aux
            );
          I_aux (I_clear (product_clear_ctyp, product_clear), _);
        ]
        when same_name exact exact_copy && same_name exact exact_clear && ctyp_equal exact_ctyp exact_copy_ctyp
             && ctyp_equal exact_ctyp exact_clear_ctyp && same_name product product_copy
             && same_name product product_arg && same_name product product_clear
             && ctyp_equal product_ctyp product_copy_ctyp
             && ctyp_equal product_ctyp product_arg_ctyp
             && ctyp_equal product_ctyp product_clear_ctyp
             && truncating_reduction_primitive modulo ->
          Option.bind (arithmetic_primitive_of_op arithmetic_op) (fun operation ->
              Option.map
                (fun modulus ->
                  let bounds =
                    ( [
                        C.integer_representation_bounds (cval_ctyp left);
                        C.integer_representation_bounds (cval_ctyp right);
                      ],
                      C.integer_representation_bounds exact_ctyp
                    )
                  in
                  ( operation,
                    Jib_semantics.Truncating,
                    modulus,
                    bounds,
                    [],
                    reduction_bounds,
                    destination,
                    left,
                    right,
                    reduction_aux
                  )
                )
                (integer_literal modulus_literal)
          )
      | [
          I_aux ((I_decl (exact_ctyp, exact) | I_reset (exact_ctyp, exact)), _);
          I_aux (I_copy (CL_id (exact_result, exact_result_ctyp), V_call (arithmetic_op, [left; right])), _);
          I_aux
            ( I_init
                ( remainder_ctyp,
                  remainder,
                  Init_cval (V_call ((Imod | Proven_imod), [V_id (exact_arg, exact_arg_ctyp); modulus_literal]))
                ),
              _
            );
          I_aux (I_copy (destination, V_id (remainder_copy, remainder_copy_ctyp)), copy_aux);
          I_aux (I_clear (remainder_clear_ctyp, remainder_clear), _);
          I_aux (I_clear (exact_clear_ctyp, exact_clear), _);
        ]
        when same_name exact exact_result && same_name exact exact_arg && same_name exact exact_clear
             && ctyp_equal exact_ctyp exact_result_ctyp && ctyp_equal exact_ctyp exact_arg_ctyp
             && ctyp_equal exact_ctyp exact_clear_ctyp && same_name remainder remainder_copy
             && same_name remainder remainder_clear
             && ctyp_equal remainder_ctyp remainder_copy_ctyp
             && ctyp_equal remainder_ctyp remainder_clear_ctyp ->
          Option.bind (arithmetic_primitive_of_op arithmetic_op) (fun operation ->
              Option.map
                (fun modulus ->
                  let bounds =
                    ( [
                        C.integer_representation_bounds (cval_ctyp left);
                        C.integer_representation_bounds (cval_ctyp right);
                      ],
                      C.integer_representation_bounds exact_ctyp
                    )
                  in
                  let reduction_bounds =
                    ( [
                        C.integer_representation_bounds exact_ctyp;
                        C.integer_representation_bounds (cval_ctyp modulus_literal);
                      ],
                      C.integer_representation_bounds remainder_ctyp
                    )
                  in
                  ( operation,
                    Jib_semantics.Truncating,
                    modulus,
                    bounds,
                    [],
                    reduction_bounds,
                    destination,
                    left,
                    right,
                    copy_aux
                  )
                )
                (integer_literal modulus_literal)
          )
      | [
          I_aux ((I_decl (exact_ctyp, exact) | I_reset (exact_ctyp, exact)), _);
          I_aux (I_copy (CL_id (exact_result, exact_result_ctyp), V_call (arithmetic_op, [left; right])), _);
          I_aux
            ( I_block
                [
                  I_aux
                    ( I_init
                        ( remainder_ctyp,
                          remainder,
                          Init_cval (V_call ((Imod | Proven_imod), [V_id (exact_arg, exact_arg_ctyp); modulus_literal]))
                        ),
                      _
                    );
                  I_aux (I_copy (destination, V_id (remainder_copy, remainder_copy_ctyp)), copy_aux);
                  I_aux (I_clear (remainder_clear_ctyp, remainder_clear), _);
                ],
              _
            );
          I_aux (I_clear (exact_clear_ctyp, exact_clear), _);
        ]
        when same_name exact exact_result && same_name exact exact_arg && same_name exact exact_clear
             && ctyp_equal exact_ctyp exact_result_ctyp && ctyp_equal exact_ctyp exact_arg_ctyp
             && ctyp_equal exact_ctyp exact_clear_ctyp && same_name remainder remainder_copy
             && same_name remainder remainder_clear
             && ctyp_equal remainder_ctyp remainder_copy_ctyp
             && ctyp_equal remainder_ctyp remainder_clear_ctyp ->
          Option.bind (arithmetic_primitive_of_op arithmetic_op) (fun operation ->
              Option.map
                (fun modulus ->
                  let bounds =
                    ( [
                        C.integer_representation_bounds (cval_ctyp left);
                        C.integer_representation_bounds (cval_ctyp right);
                      ],
                      C.integer_representation_bounds exact_ctyp
                    )
                  in
                  let reduction_bounds =
                    ( [
                        C.integer_representation_bounds exact_ctyp;
                        C.integer_representation_bounds (cval_ctyp modulus_literal);
                      ],
                      C.integer_representation_bounds remainder_ctyp
                    )
                  in
                  ( operation,
                    Jib_semantics.Truncating,
                    modulus,
                    bounds,
                    [],
                    reduction_bounds,
                    destination,
                    left,
                    right,
                    copy_aux
                  )
                )
                (integer_literal modulus_literal)
          )
      | _ -> None
    in
    let proven_native_modular_arithmetic = function
      | [
          I_aux ((I_decl (product_ctyp, product) | I_reset (product_ctyp, product)), _);
          I_aux
            ( I_block
                [
                  I_aux ((I_decl (left_ctyp, left_temporary) | I_reset (left_ctyp, left_temporary)), _);
                  I_aux (I_copy (CL_id (left_copy, left_copy_ctyp), left), _);
                  I_aux ((I_decl (right_ctyp, right_temporary) | I_reset (right_ctyp, right_temporary)), _);
                  I_aux (I_copy (CL_id (right_copy, right_copy_ctyp), right), _);
                  I_aux
                    ( I_copy
                        ( CL_id (product_result, product_result_ctyp),
                          V_call (arithmetic_op, [V_id (left_arg, left_arg_ctyp); V_id (right_arg, right_arg_ctyp)])
                        ),
                      _
                    );
                  I_aux (I_clear (right_clear_ctyp, right_clear), _);
                  I_aux (I_clear (left_clear_ctyp, left_clear), _);
                ],
              _
            );
          I_aux
            ( I_init
                ( remainder_ctyp,
                  remainder,
                  Init_cval (V_call (Proven_imod, [V_id (product_arg, product_arg_ctyp); modulus_literal]))
                ),
              _
            );
          I_aux (I_copy (destination, V_id (remainder_copy, remainder_copy_ctyp)), copy_aux);
          I_aux (I_clear (remainder_clear_ctyp, remainder_clear), _);
          I_aux (I_clear (product_clear_ctyp, product_clear), _);
        ]
        when same_name left_temporary left_copy && same_name left_temporary left_arg
             && same_name left_temporary left_clear && ctyp_equal left_ctyp left_copy_ctyp
             && ctyp_equal left_ctyp left_arg_ctyp && ctyp_equal left_ctyp left_clear_ctyp
             && same_name right_temporary right_copy && same_name right_temporary right_arg
             && same_name right_temporary right_clear && ctyp_equal right_ctyp right_copy_ctyp
             && ctyp_equal right_ctyp right_arg_ctyp && ctyp_equal right_ctyp right_clear_ctyp
             && same_name product product_result && same_name product product_arg && same_name product product_clear
             && ctyp_equal product_ctyp product_result_ctyp
             && ctyp_equal product_ctyp product_arg_ctyp
             && ctyp_equal product_ctyp product_clear_ctyp
             && same_name remainder remainder_copy && same_name remainder remainder_clear
             && ctyp_equal remainder_ctyp remainder_copy_ctyp
             && ctyp_equal remainder_ctyp remainder_clear_ctyp ->
          Option.bind (arithmetic_primitive_of_op arithmetic_op) (fun operation ->
              Option.map
                (fun modulus ->
                  let bounds =
                    ( [
                        C.integer_representation_bounds (cval_ctyp left);
                        C.integer_representation_bounds (cval_ctyp right);
                      ],
                      C.integer_representation_bounds product_ctyp
                    )
                  in
                  let reduction_bounds =
                    ( [
                        C.integer_representation_bounds product_ctyp;
                        C.integer_representation_bounds (cval_ctyp modulus_literal);
                      ],
                      C.integer_representation_bounds remainder_ctyp
                    )
                  in
                  ( operation,
                    Jib_semantics.Truncating,
                    modulus,
                    bounds,
                    [],
                    reduction_bounds,
                    destination,
                    left,
                    right,
                    copy_aux
                  )
                )
                (integer_literal modulus_literal)
          )
      | _ -> None
    in
    let direct_block_modular_arithmetic = function
      | [
          I_aux ((I_decl (result_ctyp, result) | I_reset (result_ctyp, result)), _);
          I_aux
            ( I_block
                [
                  I_aux ((I_decl (left_ctyp, left_temporary) | I_reset (left_ctyp, left_temporary)), _);
                  I_aux (I_copy (CL_id (left_copy, left_copy_ctyp), left), _);
                  I_aux ((I_decl (right_ctyp, right_temporary) | I_reset (right_ctyp, right_temporary)), _);
                  I_aux (I_copy (CL_id (right_copy, right_copy_ctyp), right), _);
                  I_aux
                    ( I_copy
                        ( CL_id (result_copy, result_copy_ctyp),
                          V_call (arithmetic_op, [V_id (left_arg, left_arg_ctyp); V_id (right_arg, right_arg_ctyp)])
                        ),
                      _
                    );
                  I_aux (I_clear (right_clear_ctyp, right_clear), _);
                  I_aux (I_clear (left_clear_ctyp, left_clear), _);
                ],
              _
            );
          I_aux
            ( I_funcall
                ( CR_one destination,
                  Call (reduction_bounds, _),
                  (modulo, _),
                  [V_id (result_arg, result_arg_ctyp); modulus_literal]
                ),
              reduction_aux
            );
          I_aux (I_clear (result_clear_ctyp, result_clear), _);
        ]
        when same_name left_temporary left_copy && same_name left_temporary left_arg
             && same_name left_temporary left_clear && ctyp_equal left_ctyp left_copy_ctyp
             && ctyp_equal left_ctyp left_arg_ctyp && ctyp_equal left_ctyp left_clear_ctyp
             && same_name right_temporary right_copy && same_name right_temporary right_arg
             && same_name right_temporary right_clear && ctyp_equal right_ctyp right_copy_ctyp
             && ctyp_equal right_ctyp right_arg_ctyp && ctyp_equal right_ctyp right_clear_ctyp
             && same_name result result_copy && same_name result result_arg && same_name result result_clear
             && ctyp_equal result_ctyp result_copy_ctyp && ctyp_equal result_ctyp result_arg_ctyp
             && ctyp_equal result_ctyp result_clear_ctyp -> (
          match
            (arithmetic_primitive_of_op arithmetic_op, reduction_primitive modulo, integer_literal modulus_literal)
          with
          | Some operation, Some reduction, Some modulus when reduction_may_observe_low_bits operation reduction ->
              let bounds =
                ( [C.integer_representation_bounds (cval_ctyp left); C.integer_representation_bounds (cval_ctyp right)],
                  C.integer_representation_bounds result_ctyp
                )
              in
              Some (operation, reduction, modulus, bounds, [], reduction_bounds, destination, left, right, reduction_aux)
          | _ -> None
        )
      | _ -> None
    in
    let direct_modular_arithmetic = function
      | [
          I_aux ((I_decl (product_ctyp, product) | I_reset (product_ctyp, product)), _);
          I_aux
            ( I_funcall
                (CR_one (CL_id (product_result, product_result_ctyp)), arithmetic_call, (multiply, _), [left; right]),
              _
            );
          I_aux
            ( I_funcall
                ( CR_one destination,
                  Call (reduction_bounds, _),
                  (modulo, _),
                  [V_id (product_arg, product_arg_ctyp); modulus_literal]
                ),
              reduction_aux
            );
          I_aux (I_clear (product_clear_ctyp, product_clear), _);
        ]
        when same_name product product_result && same_name product product_arg && same_name product product_clear
             && ctyp_equal product_ctyp product_result_ctyp
             && ctyp_equal product_ctyp product_arg_ctyp
             && ctyp_equal product_ctyp product_clear_ctyp -> (
          match (arithmetic_primitive multiply, reduction_primitive modulo) with
          | Some operation, Some reduction when reduction_may_observe_low_bits operation reduction ->
              let bounds, semantic_proofs =
                match arithmetic_call with
                | Call (bounds, semantic_proofs) -> (bounds, semantic_proofs)
                | _ ->
                    ( ( [
                          C.integer_representation_bounds (cval_ctyp left);
                          C.integer_representation_bounds (cval_ctyp right);
                        ],
                        C.integer_representation_bounds product_ctyp
                      ),
                      []
                    )
              in
              Option.map
                (fun modulus ->
                  ( operation,
                    reduction,
                    modulus,
                    bounds,
                    semantic_proofs,
                    reduction_bounds,
                    destination,
                    left,
                    right,
                    reduction_aux
                  )
                )
                (integer_literal modulus_literal)
          | _ -> None
        )
      | _ -> None
    in
    let direct_proven_modular_arithmetic = function
      | [
          I_aux ((I_decl (result_ctyp, result) | I_reset (result_ctyp, result)), _);
          I_aux
            ( I_funcall (CR_one (CL_id (result_copy, result_copy_ctyp)), arithmetic_call, (arithmetic, _), [left; right]),
              _
            );
          I_aux
            ( I_init
                ( remainder_ctyp,
                  remainder,
                  Init_cval (V_call ((Imod | Proven_imod), [V_id (result_arg, result_arg_ctyp); modulus_literal]))
                ),
              _
            );
          I_aux (I_copy (destination, V_id (remainder_copy, remainder_copy_ctyp)), copy_aux);
          I_aux (I_clear (remainder_clear_ctyp, remainder_clear), _);
          I_aux (I_clear (result_clear_ctyp, result_clear), _);
        ]
        when same_name result result_copy && same_name result result_arg && same_name result result_clear
             && ctyp_equal result_ctyp result_copy_ctyp && ctyp_equal result_ctyp result_arg_ctyp
             && ctyp_equal result_ctyp result_clear_ctyp
             && same_name remainder remainder_copy && same_name remainder remainder_clear
             && ctyp_equal remainder_ctyp remainder_copy_ctyp
             && ctyp_equal remainder_ctyp remainder_clear_ctyp -> (
          match (arithmetic_primitive arithmetic, integer_literal modulus_literal) with
          | Some operation, Some modulus ->
              let bounds, semantic_proofs =
                match arithmetic_call with
                | Call (bounds, semantic_proofs) -> (bounds, semantic_proofs)
                | _ ->
                    ( ( [
                          C.integer_representation_bounds (cval_ctyp left);
                          C.integer_representation_bounds (cval_ctyp right);
                        ],
                        C.integer_representation_bounds result_ctyp
                      ),
                      []
                    )
              in
              let reduction_bounds =
                ( [
                    C.integer_representation_bounds result_ctyp;
                    C.integer_representation_bounds (cval_ctyp modulus_literal);
                  ],
                  C.integer_representation_bounds remainder_ctyp
                )
              in
              Some
                ( operation,
                  Jib_semantics.Truncating,
                  modulus,
                  bounds,
                  semantic_proofs,
                  reduction_bounds,
                  destination,
                  left,
                  right,
                  copy_aux
                )
          | _ -> None
        )
      | _ -> None
    in
    let modular_arithmetic result arithmetic modulus_initializer_instr reduction =
      match modulus_initializer modulus_initializer_instr with
      | Some (modulus_name, modulus) -> (
          match (converted_arithmetic result arithmetic, reduced_destination result modulus_name reduction) with
          | ( Some (operation, left, right, bounds, semantic_proofs),
              Some (reduction, destination, reduction_bounds, copy_aux) )
            when reduction_may_observe_low_bits operation reduction ->
              Some
                ( operation,
                  reduction,
                  modulus,
                  bounds,
                  semantic_proofs,
                  reduction_bounds,
                  destination,
                  left,
                  right,
                  copy_aux
                )
          | _ -> None
        )
      | None -> None
    in
    let modular_arithmetic_with_embedded_modulus result arithmetic reduction =
      let fold modulus_initializer_instr reduction =
        match modulus_initializer modulus_initializer_instr with
        | Some (modulus, _) ->
            let reduction =
              match List.rev reduction with
              | I_aux (I_clear (CT_lint, modulus_clear), _) :: reduction when same_name modulus modulus_clear ->
                  List.rev reduction
              | _ -> reduction
            in
            modular_arithmetic result arithmetic modulus_initializer_instr reduction
        | None -> None
      in
      match reduction with
      | I_aux ((I_decl (CT_lint, modulus) | I_reset (CT_lint, modulus)), aux)
        :: I_aux (I_copy (CL_id (modulus_copy, CT_lint), (V_lit (VL_int _, _) as literal)), _)
        :: reduction
        when same_name modulus modulus_copy ->
          fold (I_aux (I_init (CT_lint, modulus, Init_cval literal), aux)) reduction
      | modulus_initializer_instr :: reduction -> fold modulus_initializer_instr reduction
      | [] -> None
    in
    let match_modular_arithmetic instrs =
      match widening_native_modular_arithmetic instrs with
      | Some arithmetic -> Some arithmetic
      | None -> (
          match direct_block_modular_arithmetic instrs with
          | Some arithmetic -> Some arithmetic
          | None -> (
              match direct_proven_modular_arithmetic instrs with
              | Some arithmetic -> Some arithmetic
              | None -> (
                  match proven_native_modular_arithmetic instrs with
                  | Some multiplication -> Some multiplication
                  | None -> (
                      match direct_modular_arithmetic instrs with
                      | Some multiplication -> Some multiplication
                      | None -> (
                          match instrs with
                          | [
                           I_aux ((I_decl (CT_lint, product) | I_reset (CT_lint, product)), _);
                           I_aux (I_block multiplication, _);
                           modulus_initializer_instr;
                           I_aux (I_block reduction, _);
                           I_aux (I_clear (CT_lint, modulus_clear), _);
                           I_aux (I_clear (CT_lint, product_clear), _);
                          ] -> (
                              match modulus_initializer modulus_initializer_instr with
                              | Some (modulus, _)
                                when same_name modulus modulus_clear && same_name product product_clear ->
                                  modular_arithmetic product multiplication modulus_initializer_instr reduction
                              | _ -> None
                            )
                          | [
                           I_aux ((I_decl (CT_lint, product) | I_reset (CT_lint, product)), _);
                           I_aux (I_block multiplication, _);
                           I_aux (I_block reduction, _);
                           I_aux (I_clear (CT_lint, product_clear), _);
                          ]
                            when same_name product product_clear ->
                              modular_arithmetic_with_embedded_modulus product multiplication reduction
                          | _ -> None
                        )
                    )
                )
            )
        )
    in
    let destination_matches_modulus destination modulus =
      match C.integer_representation_bounds (clexp_ctyp destination) with
      | Some (lower, upper) -> Big_int.equal lower Big_int.zero && Big_int.equal (Big_int.succ upper) modulus
      | None -> false
    in
    let semantic_operands_fit modulus = function
      | [Some (left_lower, left_upper); Some (right_lower, right_upper)], _ ->
          Big_int.less_equal Big_int.zero left_lower
          && Big_int.less left_upper modulus
          && Big_int.less_equal Big_int.zero right_lower
          && Big_int.less right_upper modulus
      | _ -> false
    in
    let power_of_two_width modulus =
      let rec loop width power =
        if Big_int.equal power modulus then Some width
        else if Big_int.greater power modulus then None
        else loop (width + 1) (Big_int.mul power (Big_int.of_int 2))
      in
      loop 0 (Big_int.of_int 1)
    in
    let wrapping_evidence = ref Jib_semantics.empty in
    let wrapping_selected = ref 0 in
    let wrapping_rejected = ref 0 in
    let log_semantic_web format =
      Printf.ksprintf
        (fun message -> if !opt_debug_function_representations then Printf.eprintf "C semantic web: %s\n%!" message)
        format
    in
    let instruction_number (I_aux (_, (number, _))) = number in
    let rec instruction_contains number (I_aux (aux, (candidate, _))) =
      candidate = number
      ||
      match aux with
      | I_block body | I_try_block body -> List.exists (instruction_contains number) body
      | I_if (_, then_body, else_body) ->
          List.exists (instruction_contains number) then_body || List.exists (instruction_contains number) else_body
      | _ -> false
    in
    let instruction_declares name = function
      | I_aux ((I_decl (_, declared) | I_reset (_, declared) | I_init (_, declared, _)), _) ->
          Name.compare name declared = 0
      | _ -> false
    in
    (* Build a semantic candidate from def-use connectivity rather than from a
       fixed instruction window.  A generated arithmetic web is rooted at the
       temporary that carries its exact result.  The primary slice follows the
       inputs needed by its consumers, without following their outputs into
       later representation wrappers.  A broader connected slice remains as a
       fallback for older JIB shapes whose remainder lifecycle is part of the
       recognizable idiom.  Instructions unrelated to either web are left out,
       so harmless scheduling and cleanup changes do not hide the transform. *)
    let dependency_candidates instrs =
      let instructions = Array.of_list instrs in
      let count = Array.length instructions in
      let declared_between first last name =
        let rec loop index = index <= last && (instruction_declares name instructions.(index) || loop (index + 1)) in
        loop first
      in
      let candidate_from seed =
        match instructions.(seed) with
        | I_aux ((I_decl (_, result) | I_reset (_, result)), _) -> (
            let build_web follow_outputs =
              let selected = Array.make count false in
              selected.(seed) <- true;
              let tracked = ref (NameSet.singleton result) in
              let changed = ref true in
              while !changed do
                changed := false;
                for index = seed to count - 1 do
                  let instr = instructions.(index) in
                  let ids = instr_ids ~direct:false instr in
                  if selected.(index) || not (NameSet.is_empty (NameSet.inter ids !tracked)) then (
                    if not selected.(index) then (
                      selected.(index) <- true;
                      changed := true
                    );
                    let dependencies =
                      if follow_outputs then
                        NameSet.union (instr_reads ~direct:false instr) (instr_writes ~direct:false instr)
                      else instr_reads ~direct:false instr
                    in
                    let tracked' =
                      NameSet.fold
                        (fun name tracked ->
                          if NameSet.mem name tracked || declared_between seed index name then NameSet.add name tracked
                          else tracked
                        )
                        dependencies !tracked
                    in
                    if not (NameSet.equal tracked' !tracked) then (
                      tracked := tracked';
                      changed := true
                    )
                  )
                done
              done;
              let web = ref [] in
              let dependencies = ref Jib_semantics.InstructionSet.empty in
              for index = 0 to count - 1 do
                if selected.(index) then (
                  web := instructions.(index) :: !web;
                  dependencies :=
                    Jib_semantics.InstructionSet.add (instruction_number instructions.(index)) !dependencies
                )
              done;
              (List.rev !web, !dependencies)
            in
            let match_web (web, dependencies) =
              match match_modular_arithmetic web with
              | Some ((_, _, _, _, _, _, _, _, _, (root, _)) as arithmetic) ->
                  let anchor =
                    match List.find_opt (instruction_contains root) web with
                    | Some instr -> instruction_number instr
                    | None -> root
                  in
                  Some (arithmetic, Jib_semantics.InstructionSet.add root dependencies, anchor)
              | None -> None
            in
            match match_web (build_web false) with
            | Some candidate -> Some candidate
            | None -> match_web (build_web true)
          )
        | _ -> None
      in
      let rec collect index candidates =
        if index = count then List.rev candidates
        else (
          match candidate_from index with
          | Some candidate -> collect (index + 1) (candidate :: candidates)
          | None -> collect (index + 1) candidates
        )
      in
      collect 0 []
    in
    let record_candidate owner dependencies = function
      | Some
          (operation, reduction, modulus, (operand_bounds, _), semantic_proofs, _, destination, left, right, (root, _))
        -> (
          let valid_modulus = Big_int.greater modulus (Big_int.of_int 1) in
          let valid_destination = destination_matches_modulus destination modulus in
          let valid_operands =
            semantic_operands_fit modulus (operand_bounds, None)
            ||
            let lower = Big_int.zero in
            let upper = Big_int.pred modulus in
            Jib_semantics.has_argument_bounds ~index:0 ~lower ~upper semantic_proofs
            && Jib_semantics.has_argument_bounds ~index:1 ~lower ~upper semantic_proofs
          in
          let valid_reduction = reduction_observes_low_bits operation reduction semantic_proofs in
          match (valid_modulus, valid_destination, valid_reduction, power_of_two_width modulus) with
          | true, true, true, Some width ->
              let fact value interval =
                let unsigned =
                  match interval with Some (lower, _) -> Big_int.less_equal Big_int.zero lower | None -> false
                in
                { Jib_semantics.logical_type = cval_ctyp value; interval; unsigned }
              in
              let operands =
                match operand_bounds with
                | [left_bounds; right_bounds] -> [fact left left_bounds; fact right right_bounds]
                | _ -> []
              in
              wrapping_evidence :=
                Jib_semantics.record
                  {
                    identity = { owner; instruction = root };
                    operation;
                    reduction;
                    observation = Jib_semantics.Low_bits width;
                    modulus;
                    operands;
                    proofs = semantic_proofs;
                    dependencies;
                  }
                  !wrapping_evidence;
              log_semantic_web "accepted function=%s instruction=%d width=%d operands-proved=%b" (string_of_id owner)
                root width valid_operands
          | _, _, _, width ->
              log_semantic_web
                "rejected function=%s instruction=%d modulus=%s destination=%b operands=%b reduction=%b power-of-two=%b"
                (string_of_id owner) root (Big_int.to_string modulus) valid_destination valid_operands valid_reduction
                (Option.is_some width)
        )
      | _ -> ()
    in
    let rec discover_candidates owner instrs =
      List.iter
        (fun (arithmetic, dependencies, _) -> record_candidate owner dependencies (Some arithmetic))
        (dependency_candidates instrs);
      List.iter
        (function
          | I_aux (I_block body, _) | I_aux (I_try_block body, _) -> discover_candidates owner body
          | I_aux (I_if (_, then_body, else_body), _) ->
              discover_candidates owner then_body;
              discover_candidates owner else_body
          | _ -> ()
          )
        instrs
    in
    List.iter
      (function CDEF_aux (CDEF_fundef (owner, _, _, body), _) -> discover_candidates owner body | _ -> ())
      cdefs;
    let represented_operand_fits modulus value =
      match C.integer_representation_bounds (cval_ctyp value) with
      | Some (lower, upper) -> Big_int.less_equal Big_int.zero lower && Big_int.less upper modulus
      | None -> false
    in
    let select_wrapping_arithmetic = function
      | Some (operation, reduction, modulus, _, _, _, destination, left, right, ((root, _) as copy_aux)) -> (
          match Jib_semantics.find ~instruction:root !wrapping_evidence with
          | Some evidence
            when evidence.operation = operation && evidence.reduction = reduction
                 && Big_int.equal evidence.modulus modulus
                 && destination_matches_modulus destination modulus
                 &&
                 let lower = Big_int.zero in
                 let upper = Big_int.pred modulus in
                 (represented_operand_fits modulus left
                 || Jib_semantics.has_argument_bounds ~index:0 ~lower ~upper evidence.proofs
                 )
                 && (represented_operand_fits modulus right
                    || Jib_semantics.has_argument_bounds ~index:1 ~lower ~upper evidence.proofs
                    ) -> (
              match evidence.observation with
              | Jib_semantics.Low_bits width ->
                  let carrier = clexp_ctyp destination in
                  let wrapping_op =
                    match operation with
                    | Jib_semantics.Add -> Wrapping_iadd width
                    | Jib_semantics.Subtract -> Wrapping_isub width
                    | Jib_semantics.Multiply -> Wrapping_imul width
                  in
                  let result =
                    match carrier with
                    | CT_fuint _ ->
                        let l = snd copy_aux in
                        let promote value =
                          if ctyp_equal (cval_ctyp value) carrier then ([], value, [])
                          else (
                            match value with
                            | V_lit (VL_int literal, _) -> ([], V_lit (VL_int literal, carrier), [])
                            | _ ->
                                let temporary = ngensym () in
                                ( [idecl l carrier temporary; icopy l (CL_id (temporary, carrier)) value],
                                  V_id (temporary, carrier),
                                  [iclear ~loc:l carrier temporary]
                                )
                          )
                        in
                        let left_setup, left, left_cleanup = promote left in
                        let right_setup, right, right_cleanup = promote right in
                        Some
                          (iblock
                             (left_setup @ right_setup
                             @ [I_aux (I_copy (destination, V_call (wrapping_op, [left; right])), copy_aux)]
                             @ right_cleanup @ left_cleanup
                             )
                          )
                    | CT_fint _ -> None
                    | _ when represented_operand_fits modulus left && represented_operand_fits modulus right ->
                        if ctyp_equal (cval_ctyp left) carrier then
                          Some (I_aux (I_copy (destination, V_call (wrapping_op, [left; right])), copy_aux))
                        else if operation <> Jib_semantics.Subtract && ctyp_equal (cval_ctyp right) carrier then
                          Some (I_aux (I_copy (destination, V_call (wrapping_op, [right; left])), copy_aux))
                        else None
                    | _ -> None
                  in
                  (match result with Some _ -> incr wrapping_selected | None -> incr wrapping_rejected);
                  result
              | Jib_semantics.Exact | Jib_semantics.Checked | Jib_semantics.Saturating -> None
            )
          | _ -> None
        )
      | None -> None
    in
    let rec rewrite_wrapping_arithmetic instrs =
      let replacements = Hashtbl.create 4 in
      let removed = ref Jib_semantics.InstructionSet.empty in
      List.iter
        (fun (arithmetic, dependencies, anchor) ->
          if not (Hashtbl.mem replacements anchor) then (
            match select_wrapping_arithmetic (Some arithmetic) with
            | Some folded ->
                Hashtbl.add replacements anchor folded;
                removed := Jib_semantics.InstructionSet.union dependencies !removed
            | None -> ()
          )
        )
        (dependency_candidates instrs);
      List.filter_map
        (fun instr ->
          let number = instruction_number instr in
          match Hashtbl.find_opt replacements number with
          | Some folded -> Some folded
          | None when Jib_semantics.InstructionSet.mem number !removed -> None
          | None -> Some (rewrite_wrapping_arithmetic_instr instr)
        )
        instrs
    and rewrite_wrapping_arithmetic_instr = function
      | I_aux (I_block body, aux) -> I_aux (I_block (rewrite_wrapping_arithmetic body), aux)
      | I_aux (I_try_block body, aux) -> I_aux (I_try_block (rewrite_wrapping_arithmetic body), aux)
      | I_aux (I_if (condition, then_body, else_body), aux) ->
          I_aux (I_if (condition, rewrite_wrapping_arithmetic then_body, rewrite_wrapping_arithmetic else_body), aux)
      | instr -> instr
    in
    let valspecs =
      List.fold_left
        (fun specs -> function
          | CDEF_aux (CDEF_val (id, tyargs, param_ctyps, ret_ctyp, extern), def_annot) ->
              Bindings.add id (tyargs, param_ctyps, ret_ctyp, extern, def_annot) specs
          | _ -> specs
          )
        Bindings.empty cdefs
    in
    (* A representation-specific implementation may also match the canonical
       function ABI exactly.  Such a function does not create a clone demand,
       because none of its parameter or result representations differ.  Give
       the backend the same single-source selection opportunity here that it
       receives for generated representation clones below. *)
    let cdefs =
      List.map
        (function
          | CDEF_aux (CDEF_fundef (id, heap_return, params, _), fundef_annot) as cdef -> (
              match Bindings.find_opt id valspecs with
              (* A spliced override is an explicit refinement of the canonical
                 function; it must win over the backend's built-in support
                 routine for the same name and ABI. *)
              | Some ([], param_ctyps, ret_ctyp, None, _) when Option.is_none (get_def_attribute "spliced" fundef_annot)
                -> (
                  match C.specialized_function_external id param_ctyps ret_ctyp with
                  | Some external_id ->
                      if List.compare_lengths params param_ctyps <> 0 then
                        Reporting.unreachable (id_loc id) __POS__
                          ("Function parameters do not match valspec for " ^ string_of_id id);
                      let l = id_loc id in
                      let args = List.map2 (fun param ctyp -> V_id (param, ctyp)) params param_ctyps in
                      let call =
                        match ifuncall l (CL_id (return, ret_ctyp)) (external_id, []) args with
                        | I_aux (I_funcall (creturn, _, fn, call_args), aux) ->
                            I_aux (I_funcall (creturn, Extern ret_ctyp, fn, call_args), aux)
                        | _ -> assert false
                      in
                      CDEF_aux (CDEF_fundef (id, heap_return, params, [call; iend l]), fundef_annot)
                  | None -> cdef
                )
              | _ -> cdef
            )
          | cdef -> cdef
          )
        cdefs
    in
    let fundefs =
      List.fold_left
        (fun fundefs -> function
          | CDEF_aux (CDEF_fundef (id, heap_return, params, body), def_annot) ->
              Bindings.add id (heap_return, params, body, def_annot) fundefs
          | _ -> fundefs
          )
        Bindings.empty cdefs
    in
    (* Preserve path refinements across boolean helper boundaries without
       changing the program's call structure.  A summary describes a pure
       relationship between a boolean result and the integer arguments of its
       source function.  It is proof metadata only: consuming a summary at a
       branch neither inserts a C bounds check nor inlines the helper.

       Summaries are inferred to a def/call-graph fixed point.  Every observed
       return must carry the same predicate; an unresolved recursive edge, a
       constant result, or conflicting return paths therefore rejects the
       summary conservatively. *)
    let predicate_summaries =
      let predicate_operand_of_literal = function
        | V_lit (VL_int _, _) as literal -> Some (Predicate_literal literal)
        | V_lit (VL_string literal, CT_string) as value when Option.is_some (Sail_lib.int_of_string_opt literal) ->
            Some (Predicate_literal value)
        | _ -> None
      in
      let predicate_operand_of_value operands value =
        match value with
        | V_id (name, _) -> NameMap.find_opt name operands
        | value -> predicate_operand_of_literal value
      in
      let instantiate_symbolic_operand operands args = function
        | Predicate_argument index -> Option.bind (List.nth_opt args index) (predicate_operand_of_value operands)
        | Predicate_literal _ as literal -> Some literal
      in
      let instantiate_symbolic_summary operands args summary =
        Option.bind (instantiate_symbolic_operand operands args summary.predicate_left) (fun predicate_left ->
            Option.map
              (fun predicate_right -> { summary with predicate_left; predicate_right })
              (instantiate_symbolic_operand operands args summary.predicate_right)
        )
      in
      let join_equal_maps left right =
        NameMap.merge
          (fun _ left right ->
            match (left, right) with Some left, Some right when left = right -> Some left | _ -> None
          )
          left right
      in
      let infer summaries params body =
        let operands =
          List.mapi (fun index parameter -> (parameter, Predicate_argument index)) params
          |> List.fold_left (fun operands (parameter, operand) -> NameMap.add parameter operand operands) NameMap.empty
        in
        let predicate_from_comparison operands comparison left right =
          Option.bind (semantic_integer_comparison comparison) (fun predicate_comparison ->
              Option.bind (predicate_operand_of_value operands left) (fun predicate_left ->
                  Option.map
                    (fun predicate_right ->
                      { predicate_comparison; predicate_left; predicate_right; predicate_comparison_when_true = true }
                    )
                    (predicate_operand_of_value operands right)
              )
          )
        in
        let rec predicate_from_value operands predicates = function
          | V_id (name, _) -> NameMap.find_opt name predicates
          | V_call (Bnot, [value]) ->
              Option.map
                (fun summary ->
                  { summary with predicate_comparison_when_true = not summary.predicate_comparison_when_true }
                )
                (predicate_from_value operands predicates value)
          | V_call (comparison, [left; right]) -> predicate_from_comparison operands comparison left right
          | _ -> None
        in
        let predicate_from_call operands predicates id args =
          match (boolean_negation_name ctx id, args) with
          | true, [value] ->
              Option.map
                (fun summary ->
                  { summary with predicate_comparison_when_true = not summary.predicate_comparison_when_true }
                )
                (predicate_from_value operands predicates value)
          | _ -> (
              match (integer_comparison_name ctx id, args) with
              | Some comparison, [left; right] -> predicate_from_comparison operands comparison left right
              | _ -> Option.bind (Bindings.find_opt id summaries) (instantiate_symbolic_summary operands args)
            )
        in
        let invalidate name (operands, predicates, observations) =
          (NameMap.remove name operands, NameMap.remove name predicates, observations)
        in
        let assign name operand predicate state =
          let operands, predicates, observations = invalidate name state in
          let operands = Option.fold ~none:operands ~some:(fun operand -> NameMap.add name operand operands) operand in
          let predicates =
            Option.fold ~none:predicates ~some:(fun predicate -> NameMap.add name predicate predicates) predicate
          in
          (operands, predicates, observations)
        in
        let assign_value name value ((operands, predicates, _) as state) =
          assign name (predicate_operand_of_value operands value) (predicate_from_value operands predicates value) state
        in
        let assign_call name id args ((operands, predicates, _) as state) =
          assign name None (predicate_from_call operands predicates id args) state
        in
        let join_state (left_operands, left_predicates, left_observations)
            (right_operands, right_predicates, right_observations) =
          ( join_equal_maps left_operands right_operands,
            join_equal_maps left_predicates right_predicates,
            left_observations @ right_observations
          )
        in
        let rec scan_instrs state = function
          | [] -> state
          | instr :: instrs -> scan_instrs (scan_instr state instr) instrs
        and scan_instr ((operands, predicates, observations) as state) (I_aux (instr, _)) =
          match instr with
          | I_init (_, name, Init_cval value) | I_reinit (_, name, value) -> assign_value name value state
          | I_init (_, name, _) | I_decl (_, name) | I_reset (_, name) | I_clear (_, name) -> invalidate name state
          | I_copy (CL_id (name, _), value) -> assign_value name value state
          | I_funcall (CR_one (CL_id (name, _)), _, (id, _), args) -> assign_call name id args state
          | I_if (_, then_body, else_body) -> join_state (scan_instrs state then_body) (scan_instrs state else_body)
          | I_block body | I_try_block body -> scan_instrs state body
          | I_end _ -> (operands, predicates, NameMap.find_opt return predicates :: observations)
          | I_return value -> (operands, predicates, predicate_from_value operands predicates value :: observations)
          | _ -> state
        in
        let _, _, observations = scan_instrs (operands, NameMap.empty, []) body in
        match observations with
        | Some summary :: observations
          when List.for_all (function Some candidate -> candidate = summary | None -> false) observations ->
            Some summary
        | [] | None :: _ | Some _ :: _ -> None
      in
      let summaries = ref Bindings.empty in
      let changed = ref true in
      while !changed do
        changed := false;
        Bindings.iter
          (fun id (_, params, body, _) ->
            if not (Bindings.mem id !summaries) then (
              match Bindings.find_opt id valspecs with
              | Some ([], parameter_ctyps, ret_ctyp, None, _)
                when ctyp_equal ret_ctyp CT_bool && List.compare_lengths params parameter_ctyps = 0 -> (
                  match infer !summaries params body with
                  | Some summary ->
                      summaries := Bindings.add id summary !summaries;
                      changed := true
                  | None -> ()
                )
              | _ -> ()
            )
          )
          fundefs
      done;
      !summaries
    in
    let call_predicate_fact id args =
      let instantiate = function
        | Predicate_argument index -> List.nth_opt args index
        | Predicate_literal literal -> Some literal
      in
      Option.bind (Bindings.find_opt id predicate_summaries) (fun summary ->
          Option.bind (instantiate summary.predicate_left) (fun left ->
              Option.map
                (fun right -> (summary.predicate_comparison, left, right, summary.predicate_comparison_when_true))
                (instantiate summary.predicate_right)
          )
      )
    in
    if !opt_debug_function_representations then
      Bindings.iter
        (fun id summary ->
          Printf.eprintf "C representation specialization: predicate-summary function=%s comparison-positive=%b\n%!"
            (string_of_id id) summary.predicate_comparison_when_true
        )
        predicate_summaries;
    (* Infer return summaries before choosing any C representation.  The
       summaries form a least fixed point over canonical function bodies: a
       call consumes the current callee summary, and each body contributes the
       union of values written to its return register.  Starting recursive
       components at [Lifetime_bottom] lets base cases establish the first
       fact without pretending that a recursive edge returns an arbitrary
       integer.  Expanding recursive summaries widen to the declared result
       domain after a few iterations. *)
    let function_return_summaries =
      let summaries = ref Bindings.empty in
      let result_domains = ref Bindings.empty in
      Bindings.iter
        (fun id (_, params, _, _) ->
          match Bindings.find_opt id valspecs with
          | Some ([], param_ctyps, ret_ctyp, None, _)
            when List.compare_lengths params param_ctyps = 0
                 && (ctyp_equal ret_ctyp CT_lint || Option.is_some (C.integer_representation_bounds ret_ctyp)) ->
              summaries := Bindings.add id Lifetime_bottom !summaries;
              result_domains := Bindings.add id (ctyp_integer_lifetime ret_ctyp) !result_domains
          | _ -> ()
        )
        fundefs;
      let widening_counts = ref Bindings.empty in
      let changed = ref true in
      while !changed do
        changed := false;
        Bindings.iter
          (fun id (_, params, body, _) ->
            match (Bindings.find_opt id valspecs, Bindings.find_opt id !summaries) with
            | Some ([], param_ctyps, _, None, _), Some prior when List.compare_lengths params param_ctyps = 0 ->
                let parameter_intervals =
                  List.map (fun ctyp -> integer_lifetime_interval (ctyp_integer_lifetime ctyp)) param_ctyps
                in
                let call_result_lifetime callee = Bindings.find_opt callee !summaries in
                let global_ranges, _ =
                  infer_integer_lifetimes ~call_result_lifetime ctx id params param_ctyps parameter_intervals body
                in
                let _, path_storage_ranges, _ =
                  infer_path_integer_lifetimes ~call_result_lifetime ~call_predicate_fact ctx id global_ranges body
                in
                let ranges = path_sensitive_storage_ranges global_ranges path_storage_ranges in
                let inferred = Option.value ~default:Lifetime_bottom (NameMap.find_opt return ranges) in
                let expanded = join_integer_lifetime prior inferred in
                if not (integer_lifetime_equal prior expanded) then (
                  let count =
                    match prior with
                    | Lifetime_bottom -> 0
                    | _ -> Option.value ~default:0 (Bindings.find_opt id !widening_counts) + 1
                  in
                  widening_counts := Bindings.add id count !widening_counts;
                  let expanded =
                    if count >= 4 then Option.value ~default:Lifetime_top (Bindings.find_opt id !result_domains)
                    else expanded
                  in
                  summaries := Bindings.add id expanded !summaries;
                  changed := true
                )
            | _ -> ()
          )
          fundefs
      done;
      !summaries
    in
    let strengthen_interval prior inferred =
      match (prior, inferred) with
      | Some (prior_lower, prior_upper), Some (inferred_lower, inferred_upper) ->
          let lower = Big_int.max prior_lower inferred_lower in
          let upper = Big_int.min prior_upper inferred_upper in
          if Big_int.less_equal lower upper then Some (lower, upper) else prior
      | (Some _ as prior), None -> prior
      | None, inferred -> inferred
    in
    let propagate_return_summary = function
      | I_aux (I_funcall (creturn, Call ((argument_intervals, result_interval), proofs), (id, tyargs), args), aux) as
        instr -> (
          match Option.bind (Bindings.find_opt id function_return_summaries) integer_lifetime_interval with
          | Some _ as inferred ->
              let result_interval = strengthen_interval result_interval inferred in
              I_aux (I_funcall (creturn, Call ((argument_intervals, result_interval), proofs), (id, tyargs), args), aux)
          | None -> instr
        )
      | instr -> instr
    in
    let cdefs = List.map (cdef_map_instr propagate_return_summary) cdefs in
    let fundefs =
      List.fold_left
        (fun fundefs -> function
          | CDEF_aux (CDEF_fundef (id, heap_return, params, body), def_annot) ->
              Bindings.add id (heap_return, params, body, def_annot) fundefs
          | _ -> fundefs
          )
        Bindings.empty cdefs
    in
    let generic_signature_for id parameter_count =
      match Bindings.find_opt id ctx.generic_signatures with
      | Some signature when List.length signature.generic_parameters = parameter_count -> signature
      | Some _ -> Reporting.unreachable (id_loc id) __POS__ ("Generic-signature arity mismatch for " ^ string_of_id id)
      | None ->
          { generic_parameters = List.init parameter_count (fun _ -> KidSet.empty); generic_result = KidSet.empty }
    in
    let function_body_representation_pairs param_ctyps ret_ctyp actual_ctyps actual_ret_ctyp =
      let result_specializes_body =
        (not (ctyp_equal ret_ctyp actual_ret_ctyp))
        && C.specialize_function_body_representation ~semantic:ret_ctyp ~represented:actual_ret_ctyp
      in
      if result_specializes_body then
        List.filter
          (fun (semantic, represented) ->
            (not (ctyp_equal semantic represented)) && C.specialize_function_body_representation ~semantic ~represented
          )
          (List.combine (param_ctyps @ [ret_ctyp]) (actual_ctyps @ [actual_ret_ctyp]))
      else []
    in
    let specialization_is_eligible _l id param_ctyps ret_ctyp actual_ctyps actual_ret_ctyp =
      let generic_signature = generic_signature_for id (List.length param_ctyps) in
      let body_representation_pairs =
        function_body_representation_pairs param_ctyps ret_ctyp actual_ctyps actual_ret_ctyp
      in
      let has_body_specialization = body_representation_pairs <> [] in
      let implicit_width_representation semantic represented =
        has_body_specialization
        && match (semantic, represented) with CT_lint, (CT_fint _ | CT_fuint _) -> true | _ -> false
      in
      let can_specialize_arguments =
        List.map
          (fun (_generic_dependencies, (semantic, represented)) ->
            if ctyp_equal semantic represented then true
            else if
              C.specialize_function_argument_representation ~semantic ~represented
              || implicit_width_representation semantic represented
            then true
            else false
          )
          (List.combine generic_signature.generic_parameters (List.combine param_ctyps actual_ctyps))
        |> List.for_all Fun.id
      in
      let can_specialize_result =
        ctyp_equal ret_ctyp actual_ret_ctyp
        || C.specialize_function_result_representation ~semantic:ret_ctyp ~represented:actual_ret_ctyp
      in
      let has_specialized_representation =
        List.exists2
          (fun semantic represented -> not (ctyp_equal semantic represented))
          (param_ctyps @ [ret_ctyp]) (actual_ctyps @ [actual_ret_ctyp])
      in
      (* Generic positions are independent representation choices.  In
         particular, a dependent result such as [range(1, len + 33)] may need
         u128 when its generic [len] argument is u64.  Requiring every
         occurrence of semantic [int] to share one C representation would
         reject that proof-backed u64 -> u128 specialization. *)
      has_specialized_representation && can_specialize_arguments && can_specialize_result
    in
    let infer_call_bounds lifetime_ranges result args ((prior_arguments, prior_result) as prior_bounds) =
      match lifetime_ranges with
      | None -> prior_bounds
      | Some ranges ->
          let strengthen prior inferred =
            match (prior, inferred) with
            | Some (prior_lower, prior_upper), Some (inferred_lower, inferred_upper) ->
                let lower = Big_int.max prior_lower inferred_lower in
                let upper = Big_int.min prior_upper inferred_upper in
                (* Both bounds are independently established semantic facts.
                   A non-empty intersection is therefore strictly stronger
                   than either one.  Empty intersections denote an
                   unreachable call edge; retaining the source call metadata
                   is conservative until reachability is represented
                   explicitly in the path domain. *)
                if Big_int.less_equal lower upper then Some (lower, upper) else prior
            | (Some _ as prior), None -> prior
            | None, inferred -> inferred
          in
          let argument_intervals =
            if List.compare_lengths prior_arguments args = 0 then
              List.map2
                (fun prior argument ->
                  strengthen prior (integer_lifetime_interval (cval_integer_lifetime ranges argument))
                )
                prior_arguments args
            else List.map (fun argument -> integer_lifetime_interval (cval_integer_lifetime ranges argument)) args
          in
          let result_interval =
            match result with
            | CL_id (name, ctyp) ->
                let inferred =
                  match NameMap.find_opt name ranges with
                  | Some lifetime -> integer_lifetime_interval lifetime
                  | None -> integer_lifetime_interval (ctyp_integer_lifetime ctyp)
                in
                strengthen prior_result inferred
            | _ -> prior_result
          in
          (argument_intervals, result_interval)
    in
    let normalize_call_bounds generic_signature param_ctyps (argument_bounds, _) =
      let useful_bound semantic bound =
        match (bound, integer_lifetime_interval (ctyp_integer_lifetime semantic)) with
        | Some (lower, upper), Some (semantic_lower, semantic_upper)
          when Big_int.less_equal semantic_lower lower && Big_int.less_equal upper semantic_upper ->
            if Big_int.equal lower semantic_lower && Big_int.equal upper semantic_upper then None else bound
        | Some _, None -> bound
        | Some _, Some _ | None, _ -> None
      in
      ( List.map2
          (fun (generic_dependencies, semantic) bound ->
            let bound = useful_bound semantic bound in
            if ctyp_equal semantic CT_lint || position_is_generic generic_dependencies || Option.is_some bound then
              bound
            else None
          )
          (List.combine generic_signature.generic_parameters param_ctyps)
          argument_bounds,
        None
      )
    in
    let module RepresentationDemandMap = Map.Make (struct
      (* The first component is the complete representation fingerprint for a
         specialized body.  The bounds component is the seed of one compatible
         caller partition.  Keeping it in the key lets two call-graph paths use
         the same C signature and even the same pointwise body representations
         without forcing their interval hull into a representation that is no
         longer valid for either clone. *)
      type t =
        ( ctyp list
        * (name * ctyp option) list
        * ctyp option list
        * (int * id * ctyp list * ctyp * callsite_bounds) list
        * (int * bool) list
        )
        * callsite_bounds

      let compare = Stdlib.compare
    end) in
    let module RepresentationDemand = struct
      type t = {
        specialized_id : id;
        actual_ctyps : ctyp list;
        actual_ret_ctyp : ctyp;
        bounds : callsite_bounds ref;
        lifetime_ranges : integer_lifetime NameMap.t ref;
        path_lifetime_ranges : integer_lifetime NameMap.t PathInstructionMap.t ref;
        path_decisions : bool PathInstructionMap.t ref;
        lifetime_writes : ctyp NameMap.t;
        queued : bool ref;
      }
    end in
    let demanded = ref Bindings.empty in
    let pending = Queue.create () in
    let total_demands = ref 0 in
    let processed_demands = ref 0 in
    let debug_demands = !opt_debug_function_representations in
    let started_at = Sys.time () in
    let log_progress format =
      Printf.ksprintf
        (fun message ->
          if debug_demands then
            Printf.eprintf "C representation specialization: %s (%.2fs)\n%!" message (Sys.time () -. started_at)
        )
        format
    in
    let string_of_call_bounds (arguments, result) =
      "args=["
      ^ Util.string_of_list "," string_of_integer_interval arguments
      ^ "] result=" ^ string_of_integer_interval result
    in
    log_progress "start definitions=%d functions=%d" (List.length cdefs) (Bindings.cardinal fundefs);
    List.iter
      (fun evidence ->
        let operation =
          match evidence.Jib_semantics.operation with
          | Jib_semantics.Add -> "add"
          | Jib_semantics.Subtract -> "sub"
          | Jib_semantics.Multiply -> "mul"
        in
        let observation =
          match evidence.Jib_semantics.observation with
          | Jib_semantics.Low_bits width -> "low-bits:" ^ string_of_int width
          | Jib_semantics.Exact -> "exact"
          | Jib_semantics.Checked -> "checked"
          | Jib_semantics.Saturating -> "saturating"
        in
        log_progress "semantic-web discovered function=%s instruction=%d operation=%s observation=%s"
          (string_of_id evidence.Jib_semantics.identity.owner)
          evidence.Jib_semantics.identity.instruction operation observation
      )
      (Jib_semantics.bindings !wrapping_evidence);
    if debug_demands then
      Bindings.iter
        (fun id signature ->
          log_progress "generic-signature function=%s args=[%s] result=%b" (string_of_id id)
            (Util.string_of_list ","
               (fun dependencies -> string_of_bool (position_is_generic dependencies))
               signature.generic_parameters
            )
            (position_is_generic signature.generic_result)
        )
        ctx.generic_signatures;
    let analyze_demand id actual_ctyps (actual_intervals, _) =
      let _, params, body, _ = Bindings.find id fundefs in
      let lifetime_ranges, lifetime_writes = infer_integer_lifetimes ctx id params actual_ctyps actual_intervals body in
      let path_lifetime_ranges, path_storage_ranges, path_decisions =
        infer_path_integer_lifetimes ~call_predicate_fact ctx id lifetime_ranges body
      in
      let lifetime_ranges = path_sensitive_storage_ranges lifetime_ranges path_storage_ranges in
      let value_representations =
        NameMap.bindings lifetime_writes
        |> List.filter_map (fun (name, semantic) ->
            match semantic with
            | CT_lint ->
                let represented =
                  Option.bind (NameMap.find_opt name lifetime_ranges) (represented_integer_lifetime ctx)
                in
                Some (name, represented)
            | _ -> None
        )
      in
      let value_primitive_representation lifetime_ranges representations = function
        | V_call ((Iadd | Proven_iadd | Widening_iadd _ | Wrapping_iadd _), [left; right]) ->
            represented_integer_lifetime ctx
              (integer_primitive_carrier_lifetime `Add
                 (cval_integer_lifetime lifetime_ranges left)
                 (cval_integer_lifetime lifetime_ranges right)
              )
            :: representations
        | V_call ((Isub | Proven_isub | Wrapping_isub _), [left; right]) ->
            represented_integer_lifetime ctx
              (integer_primitive_carrier_lifetime `Sub
                 (cval_integer_lifetime lifetime_ranges left)
                 (cval_integer_lifetime lifetime_ranges right)
              )
            :: representations
        | V_call ((Imul | Proven_imul | Widening_imul _ | Wrapping_imul _), [left; right]) ->
            represented_integer_lifetime ctx
              (integer_primitive_carrier_lifetime `Mul
                 (cval_integer_lifetime lifetime_ranges left)
                 (cval_integer_lifetime lifetime_ranges right)
              )
            :: representations
        | V_call ((Idiv | Proven_idiv), [left; right]) ->
            represented_integer_lifetime ctx
              (integer_primitive_carrier_lifetime `Div
                 (cval_integer_lifetime lifetime_ranges left)
                 (cval_integer_lifetime lifetime_ranges right)
              )
            :: representations
        | V_call ((Imod | Proven_imod), [left; right]) ->
            represented_integer_lifetime ctx
              (integer_primitive_carrier_lifetime `Mod
                 (cval_integer_lifetime lifetime_ranges left)
                 (cval_integer_lifetime lifetime_ranges right)
              )
            :: representations
        | V_call ((Power_of_two_idiv _ | Power_of_two_imod _), [value]) ->
            represented_integer_lifetime ctx (cval_integer_lifetime lifetime_ranges value) :: representations
        | V_call ((Mixed_proven_idiv (_, result_ctyp) | Mixed_proven_imod (_, result_ctyp)), [_; _]) ->
            Some result_ctyp :: representations
        | _ -> representations
      in
      let rec primitive_representations representations (I_aux (instr, (instruction, _)) as whole_instr) =
        let instruction_ranges = instruction_lifetime_ranges lifetime_ranges path_lifetime_ranges whole_instr in
        if not (PathInstructionMap.mem instruction path_lifetime_ranges) then representations
        else (
          match instr with
          | I_funcall (CR_one _, _, (primitive_id, _), [left; right]) -> (
              match integer_primitive_name ctx primitive_id with
              | Some primitive ->
                  let carrier =
                    integer_primitive_carrier_lifetime primitive
                      (cval_integer_lifetime instruction_ranges left)
                      (cval_integer_lifetime instruction_ranges right)
                  in
                  represented_integer_lifetime ctx carrier :: representations
              | None -> representations
            )
          | I_if (_, then_instrs, else_instrs) ->
              List.fold_left primitive_representations
                (List.fold_left primitive_representations representations then_instrs)
                else_instrs
          | I_block instrs | I_try_block instrs -> List.fold_left primitive_representations representations instrs
          | I_init (_, _, Init_cval value) | I_reinit (_, _, value) | I_copy (_, value) ->
              value_primitive_representation instruction_ranges representations value
          | _ -> representations
        )
      in
      let primitive_representations = List.fold_left primitive_representations [] body |> List.rev in
      (* Bounds that reach another local function are part of this body's
         specialization outcome.  Two callers may select the same local and
         primitive carriers while sending materially different proof states
         further down the call graph.  Keeping those edges in the fingerprint
         prevents a wider partition from swallowing a stricter caller before
         the callee has had a chance to specialize. *)
      let rec call_edges edges (I_aux (instr, (instruction, _)) as whole_instr) =
        let instruction_ranges = instruction_lifetime_ranges lifetime_ranges path_lifetime_ranges whole_instr in
        if not (PathInstructionMap.mem instruction path_lifetime_ranges) then edges
        else (
          match instr with
          | I_funcall (CR_one result, Call (bounds, _), (callee, []), args) -> (
              match (Bindings.find_opt callee valspecs, Bindings.find_opt callee fundefs) with
              | Some ([], param_ctyps, _, None, _), Some _ when List.compare_lengths args param_ctyps = 0 ->
                  let generic_signature = generic_signature_for callee (List.length param_ctyps) in
                  let bounds =
                    infer_call_bounds (Some instruction_ranges) result args bounds
                    |> normalize_call_bounds generic_signature param_ctyps
                  in
                  (instruction, callee, List.map cval_ctyp args, clexp_ctyp result, bounds) :: edges
              | _ -> edges
            )
          | I_if (_, then_instrs, else_instrs) ->
              List.fold_left call_edges (List.fold_left call_edges edges then_instrs) else_instrs
          | I_block instrs | I_try_block instrs -> List.fold_left call_edges edges instrs
          | _ -> edges
        )
      in
      let call_edges = List.fold_left call_edges [] body |> List.rev in
      ( lifetime_ranges,
        path_lifetime_ranges,
        path_decisions,
        lifetime_writes,
        value_representations,
        primitive_representations,
        call_edges
      )
    in
    let semantic_bounds_specialize_body id _generic_signature actual_ctyps ((argument_bounds, _) as bounds) =
      (* A semantic interval is independently useful even when it does not
         change the function's C ABI.  Demand a clone only when projecting the
         interval through the body changes a stored value or primitive
         carrier; otherwise the canonical body is already equally precise. *)
      let has_refined_bound = List.exists Option.is_some argument_bounds in
      if not has_refined_bound then false
      else (
        let _, _, bounded_decisions, _, bounded_values, bounded_primitives, bounded_calls =
          analyze_demand id actual_ctyps bounds
        in
        let source_bounds = (List.map (fun _ -> None) argument_bounds, None) in
        let _, _, source_decisions, _, source_values, source_primitives, source_calls =
          analyze_demand id actual_ctyps source_bounds
        in
        log_progress "body-bounds function=%s bounded-primitives=[%s] source-primitives=[%s]" (string_of_id id)
          (Util.string_of_list "," (Option.fold ~none:"unbounded" ~some:string_of_ctyp) bounded_primitives)
          (Util.string_of_list "," (Option.fold ~none:"unbounded" ~some:string_of_ctyp) source_primitives);
        Stdlib.compare bounded_values source_values <> 0
        || Stdlib.compare bounded_primitives source_primitives <> 0
        || Stdlib.compare bounded_calls source_calls <> 0
        || Stdlib.compare (PathInstructionMap.bindings bounded_decisions) (PathInstructionMap.bindings source_decisions)
           <> 0
      )
    in
    let merge_interval left right =
      match (left, right) with
      | Some (left_lower, left_upper), Some (right_lower, right_upper) ->
          Some (Big_int.min left_lower right_lower, Big_int.max left_upper right_upper)
      | None, _ | _, None -> None
    in
    let merge_call_bounds (left_arguments, left_result) (right_arguments, right_result) =
      (List.map2 merge_interval left_arguments right_arguments, merge_interval left_result right_result)
    in
    let call_arguments_within (inner_arguments, _) (outer_arguments, _) =
      List.compare_lengths inner_arguments outer_arguments = 0
      && List.for_all2
           (fun inner outer ->
             match (inner, outer) with
             | _, None -> true
             | Some (inner_lower, inner_upper), Some (outer_lower, outer_upper) ->
                 Big_int.less_equal outer_lower inner_lower && Big_int.less_equal inner_upper outer_upper
             | None, Some _ -> false
           )
           inner_arguments outer_arguments
    in
    let demand l id actual_ctyps actual_ret_ctyp bounds =
      let signature_ctyps = actual_ctyps @ [actual_ret_ctyp] in
      let ( lifetime_ranges,
            path_lifetime_ranges,
            path_decisions,
            lifetime_writes,
            value_representations,
            primitive_representations,
            call_edges ) =
        analyze_demand id actual_ctyps bounds
      in
      let path_decision_fingerprint = PathInstructionMap.bindings path_decisions in
      let signature =
        (signature_ctyps, value_representations, primitive_representations, call_edges, path_decision_fingerprint)
      in
      let prior = Option.value ~default:RepresentationDemandMap.empty (Bindings.find_opt id !demanded) in
      let compatible_partition =
        RepresentationDemandMap.bindings prior
        |> List.find_map (fun (((candidate_signature, _) as key), candidate) ->
            if Stdlib.compare candidate_signature signature <> 0 then None
            else (
              let merged_bounds = merge_call_bounds !(candidate.RepresentationDemand.bounds) bounds in
              if Stdlib.compare merged_bounds !(candidate.RepresentationDemand.bounds) = 0 then
                Some
                  ( key,
                    candidate,
                    merged_bounds,
                    !(candidate.RepresentationDemand.lifetime_ranges),
                    !(candidate.RepresentationDemand.path_lifetime_ranges),
                    !(candidate.RepresentationDemand.path_decisions)
                  )
              else (
                let ( merged_ranges,
                      merged_path_ranges,
                      merged_path_decisions,
                      _,
                      merged_values,
                      merged_primitives,
                      merged_calls ) =
                  analyze_demand id actual_ctyps merged_bounds
                in
                if
                  Stdlib.compare merged_values value_representations = 0
                  && Stdlib.compare merged_primitives primitive_representations = 0
                  && Stdlib.compare merged_calls call_edges = 0
                  && Stdlib.compare (PathInstructionMap.bindings merged_path_decisions) path_decision_fingerprint = 0
                then Some (key, candidate, merged_bounds, merged_ranges, merged_path_ranges, merged_path_decisions)
                else None
              )
            )
        )
      in
      match compatible_partition with
      | Some (key, demand, merged_bounds, merged_ranges, merged_path_ranges, merged_path_decisions) ->
          if Stdlib.compare merged_bounds !(demand.RepresentationDemand.bounds) <> 0 then (
            demand.RepresentationDemand.bounds := merged_bounds;
            demand.RepresentationDemand.lifetime_ranges := merged_ranges;
            demand.RepresentationDemand.path_lifetime_ranges := merged_path_ranges;
            demand.RepresentationDemand.path_decisions := merged_path_decisions;
            if not !(demand.RepresentationDemand.queued) then (
              demand.RepresentationDemand.queued := true;
              Queue.add (id, key) pending
            )
          );
          demand.RepresentationDemand.specialized_id
      | None ->
          let key = (signature, bounds) in
          let specialized_id = mangle_representation_id id ctx signature_ctyps bounds in
          incr total_demands;
          let variants = RepresentationDemandMap.cardinal prior + 1 in
          if !total_demands <= 20 || !total_demands mod 25 = 0 || variants >= 8 then
            log_progress "demanded=%d queued=%d function=%s variants=%d %s" !total_demands
              (Queue.length pending + 1)
              (string_of_id id) variants (string_of_call_bounds bounds);
          if RepresentationDemandMap.cardinal prior >= !opt_max_function_specializations then
            raise
              (Reporting.err_general l
                 (Printf.sprintf "Function %s requires more than %d C representation specializations" (string_of_id id)
                    !opt_max_function_specializations
                 )
              );
          let demand : RepresentationDemand.t =
            {
              specialized_id;
              actual_ctyps;
              actual_ret_ctyp;
              bounds = ref bounds;
              lifetime_ranges = ref lifetime_ranges;
              path_lifetime_ranges = ref path_lifetime_ranges;
              path_decisions = ref path_decisions;
              lifetime_writes;
              queued = ref true;
            }
          in
          demanded := Bindings.add id (RepresentationDemandMap.add key demand prior) !demanded;
          Queue.add (id, key) pending;
          specialized_id
    in
    let rewrite_call ?lifetime_ranges ?current_specialization = function
      | I_aux (I_funcall ((CR_one result as creturn), Call (bounds, semantic_proofs), (id, []), args), (n, l)) as instr
        -> (
          match (Bindings.find_opt id valspecs, Bindings.find_opt id fundefs) with
          | Some ([], param_ctyps, ret_ctyp, None, _), Some _ when List.compare_lengths args param_ctyps = 0 ->
              let bounds = infer_call_bounds lifetime_ranges result args bounds in
              log_progress "call-edge instruction=%d caller=%s bounds=%s" n
                (Option.fold ~none:"canonical" ~some:(fun (id, _, _, _, _) -> string_of_id id) current_specialization)
                (string_of_call_bounds bounds);
              let actual_ctyps = List.map cval_ctyp args in
              let actual_ret_ctyp = clexp_ctyp result in
              let generic_signature = generic_signature_for id (List.length param_ctyps) in
              let bounds = normalize_call_bounds generic_signature param_ctyps bounds in
              (* Even when the callee already has its final representation and
                 needs no clone, the later precise-call pass consumes these
                 path-refined bounds to prove argument conversions safe. *)
              let instr = I_aux (I_funcall (creturn, Call (bounds, semantic_proofs), (id, []), args), (n, l)) in
              let representation_eligible =
                specialization_is_eligible l id param_ctyps ret_ctyp actual_ctyps actual_ret_ctyp
              in
              let bounds_eligible = semantic_bounds_specialize_body id generic_signature actual_ctyps bounds in
              let same_representation =
                List.for_all2 ctyp_equal param_ctyps actual_ctyps && ctyp_equal ret_ctyp actual_ret_ctyp
              in
              (* Bounds-only clones rewrite the canonical JIB body using the
                 call site's parameter representations.  That is sound only
                 when those representations already match the callee ABI;
                 otherwise an earlier fixed-width lowering in the body can
                 become ill-typed (for example [Slice] over [CT_lint]).  Keep
                 the canonical callee in that case.  The precise-call pass
                 below still consumes [bounds] and inserts the proved edge
                 conversion. *)
              let eligible = representation_eligible || (bounds_eligible && same_representation) in
              if eligible then (
                let specialized_id =
                  match current_specialization with
                  | Some (current_id, current_specialized_id, current_ctyps, current_ret_ctyp, current_bounds)
                    when Id.compare id current_id = 0 ->
                      let same_representation =
                        List.compare_lengths actual_ctyps current_ctyps = 0
                        && List.for_all2 ctyp_equal actual_ctyps current_ctyps
                        && ctyp_equal actual_ret_ctyp current_ret_ctyp
                      in
                      if same_representation && call_arguments_within bounds current_bounds then current_specialized_id
                      else if same_representation then
                        (* A recursive edge which escapes the proof partition
                           of its current clone must not reuse any branches
                           pruned by that partition.  Re-analyze it at the
                           represented signature's complete bounds.  This
                           yields one safe recursion fallback rather than one
                           clone per increasing or decreasing singleton. *)
                        demand l id actual_ctyps actual_ret_ctyp (List.map (fun _ -> None) actual_ctyps, None)
                      else demand l id actual_ctyps actual_ret_ctyp bounds
                  | _ -> demand l id actual_ctyps actual_ret_ctyp bounds
                in
                I_aux (I_funcall (creturn, Call (bounds, semantic_proofs), (specialized_id, []), args), (n, l))
              )
              else (
                if
                  debug_demands
                  && List.exists2
                       (fun semantic represented -> not (ctyp_equal semantic represented))
                       (param_ctyps @ [ret_ctyp]) (actual_ctyps @ [actual_ret_ctyp])
                then
                  log_progress "ineligible function=%s semantic=[%s]->%s represented=[%s]->%s" (string_of_id id)
                    (Util.string_of_list "," string_of_ctyp param_ctyps)
                    (string_of_ctyp ret_ctyp)
                    (Util.string_of_list "," string_of_ctyp actual_ctyps)
                    (string_of_ctyp actual_ret_ctyp);
                instr
              )
          | _ -> instr
        )
      | instr -> instr
    in
    (* Function bodies are rewritten below, after their whole-lifetime and
       path-sensitive ranges have been inferred.  Rewriting them eagerly here
       would freeze a call into a wide clone before a guarding branch can
       contribute its tighter edge proof.  Non-function definitions have no
       such local control-flow analysis, so retain eager demand discovery for
       their initializer instructions. *)
    let cdefs =
      List.rev_map
        (function
          | CDEF_aux (CDEF_fundef _, _) as cdef -> cdef
          | cdef -> cdef_map_instr (rewrite_call ?lifetime_ranges:None) cdef
          )
        cdefs
      |> List.rev
    in
    let generated = ref Bindings.empty in
    let specialized_ctx = ref ctx in
    let remove_unused_literal_temporaries body =
      let candidates = ref NameSet.empty in
      List.iter
        (iter_instr (function
          | I_aux (I_init (_, name, Init_cval (V_lit _)), _) -> candidates := NameSet.add name !candidates
          | _ -> ()
          ))
        body;
      let has_disallowed_reference name =
        let disallowed = ref false in
        List.iter
          (iter_instr (fun instr ->
               match instr with
               | I_aux (I_init (_, candidate, Init_cval (V_lit _)), _)
               | I_aux (I_decl (_, candidate), _)
               | I_aux (I_clear (_, candidate), _)
                 when Name.compare name candidate = 0 ->
                   ()
               | _
                 when instr_references ~read:name ~direct:true instr || instr_references ~write:name ~direct:true instr
                 ->
                   disallowed := true
               | _ -> ()
           )
          )
          body;
        !disallowed
      in
      let unused = NameSet.filter (fun name -> not (has_disallowed_reference name)) !candidates in
      let rec rewrite instrs =
        List.filter_map
          (fun (I_aux (instr, aux) as original) ->
            match instr with
            | (I_init (_, name, Init_cval (V_lit _)) | I_decl (_, name) | I_clear (_, name))
              when NameSet.mem name unused ->
                None
            | I_block instrs -> Some (I_aux (I_block (rewrite instrs), aux))
            | I_try_block instrs -> Some (I_aux (I_try_block (rewrite instrs), aux))
            | I_if (condition, then_instrs, else_instrs) ->
                Some (I_aux (I_if (condition, rewrite then_instrs, rewrite else_instrs), aux))
            | _ -> Some original
          )
          instrs
      in
      rewrite body
    in
    let as_unsigned_representation = function
      | value when match cval_ctyp value with CT_fuint _ -> true | _ -> false -> Some value
      | V_lit (VL_int literal, _)
        when Big_int.less_equal Big_int.zero literal
             && Big_int.less_equal literal (Big_int.pred (Big_int.pow_int_positive 2 64)) ->
          Some (V_lit (VL_int literal, CT_fuint 64))
      | value -> (
          match C.integer_representation_bounds (cval_ctyp value) with
          | Some (lower, _) when Big_int.equal lower Big_int.zero -> Some value
          | Some _ | None -> None
        )
    in
    let integer_representation_matches represented value =
      ctyp_equal (cval_ctyp value) represented
      ||
      match (C.integer_representation_bounds (cval_ctyp value), C.integer_representation_bounds represented) with
      | Some (value_lower, value_upper), Some (represented_lower, represented_upper) ->
          Big_int.equal value_lower represented_lower && Big_int.equal value_upper represented_upper
      | Some _, None | None, Some _ | None, None -> false
    in
    let proven_native_conversion represented lifetime value =
      proven_fixed_integer_conversion represented (integer_lifetime_interval lifetime) value
    in
    let specialize_proven_integer_conversion lifetime_ranges = function
      | I_aux (I_init (represented, name, Init_cval value), aux) as instr ->
          let source = cval_ctyp value in
          if ctyp_equal source represented then instr
          else (
            let lifetime = cval_integer_lifetime lifetime_ranges value in
            let converted = proven_native_conversion represented lifetime value in
            if !opt_debug_function_representations then
              Printf.eprintf
                "C representation specialization: conversion source=%s destination=%s interval=%s proof=%b\n%!"
                (string_of_ctyp source) (string_of_ctyp represented)
                (string_of_integer_interval (integer_lifetime_interval lifetime))
                (Option.is_some converted);
            Option.fold ~none:instr
              ~some:(fun value -> I_aux (I_init (represented, name, Init_cval value), aux))
              converted
          )
      | I_aux (I_reinit (represented, name, value), aux) as instr ->
          let source = cval_ctyp value in
          if ctyp_equal source represented then instr
          else (
            let lifetime = cval_integer_lifetime lifetime_ranges value in
            let converted = proven_native_conversion represented lifetime value in
            if !opt_debug_function_representations then
              Printf.eprintf
                "C representation specialization: conversion source=%s destination=%s interval=%s proof=%b\n%!"
                (string_of_ctyp source) (string_of_ctyp represented)
                (string_of_integer_interval (integer_lifetime_interval lifetime))
                (Option.is_some converted);
            Option.fold ~none:instr ~some:(fun value -> I_aux (I_reinit (represented, name, value), aux)) converted
          )
      | I_aux (I_copy (result, value), aux) as instr ->
          let represented = clexp_ctyp result in
          let source = cval_ctyp value in
          if ctyp_equal source represented then instr
          else (
            let lifetime = cval_integer_lifetime lifetime_ranges value in
            let converted = proven_native_conversion represented lifetime value in
            if !opt_debug_function_representations then
              Printf.eprintf
                "C representation specialization: conversion source=%s destination=%s interval=%s proof=%b\n%!"
                (string_of_ctyp source) (string_of_ctyp represented)
                (string_of_integer_interval (integer_lifetime_interval lifetime))
                (Option.is_some converted);
            Option.fold ~none:instr ~some:(fun value -> I_aux (I_copy (result, value), aux)) converted
          )
      | instr -> instr
    in
    let specialize_proven_bitvector_shift lifetime_ranges = function
      | I_aux (I_copy (result, V_call (((Bvshiftl | Bvshiftr | Bvarith_shiftr) as op), [value; amount])), aux) as instr
        -> (
          match cval_ctyp value with
          | CT_fbits width when 0 < width && width <= 64 ->
              let interval = integer_lifetime_interval (cval_integer_lifetime lifetime_ranges amount) in
              let proof = Jib_semantics.prove_shift_count_interval ~index:1 ~interval ~carrier_width:64 in
              if Jib_semantics.has_shift_count_bounds ~index:1 ~carrier_width:64 (Option.to_list proof) then (
                let op =
                  match op with
                  | Bvshiftl -> Proven_bvshiftl 64
                  | Bvshiftr -> Proven_bvshiftr 64
                  | Bvarith_shiftr -> Proven_bvarith_shiftr 64
                  | _ -> assert false
                in
                I_aux (I_copy (result, V_call (op, [value; amount])), aux)
              )
              else instr
          | _ -> instr
        )
      | instr -> instr
    in
    let specialize_proven_bitvector_slice lifetime_ranges = function
      | I_aux (I_copy (result, V_call (Slice width, [value; start])), aux) as instr ->
          let scalar_source =
            match cval_ctyp value with
            | CT_fbits source_width -> 0 < source_width && source_width <= 64
            | CT_sbits 64 | CT_fuint _ -> true
            | _ -> false
          in
          if scalar_source then (
            let interval = integer_lifetime_interval (cval_integer_lifetime lifetime_ranges start) in
            let proof = Jib_semantics.prove_shift_count_interval ~index:1 ~interval ~carrier_width:64 in
            if Jib_semantics.has_shift_count_bounds ~index:1 ~carrier_width:64 (Option.to_list proof) then
              I_aux (I_copy (result, V_call (Proven_slice (width, 64), [value; start])), aux)
            else instr
          )
          else instr
      | instr -> instr
    in
    let plain_fixed_vector_element = function
      | CT_unit | CT_bool | CT_fint _ | CT_fuint _ | CT_float _ | CT_rounding_mode | CT_fbits _ | CT_sbits _
      | CT_constant _ | CT_enum _ ->
          true
      | _ -> false
    in
    let specialize_proven_fixed_vector_access lifetime_ranges = function
      | I_aux (I_funcall (CR_one result, _, (id, _), [vector; index]), aux) as instr
        when C.specialize_c
             &&
             match string_of_id id with
             | "vector_access" | "vector_access_inc" | "fast_vector_access" | "fast_unsigned_vector_access" -> true
             | _ -> false -> (
          match cval_ctyp vector with
          | CT_fvector (length, element_ctyp)
            when 0 < length && plain_fixed_vector_element element_ctyp && ctyp_equal (clexp_ctyp result) element_ctyp
            -> (
              match integer_lifetime_interval (cval_integer_lifetime lifetime_ranges index) with
              | Some (lower, upper)
                when Big_int.less_equal Big_int.zero lower && Big_int.less upper (Big_int.of_int length) ->
                  I_aux (I_copy (result, V_call (Proven_vector_access length, [vector; index])), aux)
              | Some _ | None -> instr
            )
          | _ -> instr
        )
      | instr -> instr
    in
    let mixed_custom_unsigned_representations left right =
      let has_custom_unsigned_representation value =
        match cval_ctyp value with
        | CT_fuint _ -> false
        | ctyp -> (
            match C.integer_representation_bounds ctyp with
            | Some (lower, _) -> Big_int.equal lower Big_int.zero
            | None -> false
          )
      in
      match (as_unsigned_representation left, as_unsigned_representation right) with
      | Some left, Some right
        when (not (ctyp_equal (cval_ctyp left) (cval_ctyp right)))
             && (has_custom_unsigned_representation left || has_custom_unsigned_representation right) ->
          Some (left, right)
      | Some _, Some _ | None, _ | _, None -> None
    in
    let exact_mixed_unsigned_representations represented left right =
      match mixed_custom_unsigned_representations left right with
      | Some (left, right)
        when integer_representation_matches represented left || integer_representation_matches represented right ->
          Some (left, right)
      | Some _ | None -> None
    in
    let specialize_structural_integer_primitive lifetime_ranges = function
      | I_aux (I_copy (result, V_call (op, [left; right])), aux) as instr -> (
          let primitive =
            match op with
            | Iadd | Proven_iadd | Widening_iadd _ -> Some `Add
            | Isub | Proven_isub -> Some `Sub
            | Imul | Proven_imul | Widening_imul _ -> Some `Mul
            | Idiv | Proven_idiv -> Some `Div
            | Imod | Proven_imod -> Some `Mod
            | _ -> None
          in
          match primitive with
          | None -> instr
          | Some primitive -> (
              let left_lifetime = cval_integer_lifetime lifetime_ranges left in
              let right_lifetime = cval_integer_lifetime lifetime_ranges right in
              let carrier_lifetime = integer_primitive_carrier_lifetime primitive left_lifetime right_lifetime in
              match represented_integer_lifetime ctx carrier_lifetime with
              | Some ((CT_fint _ | CT_fuint _) as carrier) when not (ctyp_equal (clexp_ctyp result) carrier) ->
                  let l = snd aux in
                  log_progress "structural-primitive carrier=%s left=%s(%s) right=%s(%s)" (string_of_ctyp carrier)
                    (string_of_ctyp (cval_ctyp left))
                    (string_of_integer_interval (integer_lifetime_interval left_lifetime))
                    (string_of_ctyp (cval_ctyp right))
                    (string_of_integer_interval (integer_lifetime_interval right_lifetime));
                  let promote lifetime value =
                    if ctyp_equal (cval_ctyp value) carrier then ([], value, [])
                    else (
                      match (proven_native_conversion carrier lifetime value, value) with
                      | Some converted, _ -> ([], converted, [])
                      | _, V_lit (VL_int literal, _) -> ([], V_lit (VL_int literal, carrier), [])
                      | _, _ ->
                          let temporary = ngensym () in
                          ( [idecl l carrier temporary; icopy l (CL_id (temporary, carrier)) value],
                            V_id (temporary, carrier),
                            [iclear ~loc:l carrier temporary]
                          )
                    )
                  in
                  let left_setup, left, left_cleanup = promote left_lifetime left in
                  let right_setup, right, right_cleanup = promote right_lifetime right in
                  let represented_op =
                    match primitive with
                    | `Add -> Proven_iadd
                    | `Sub -> Proven_isub
                    | `Mul -> Proven_imul
                    | `Div | `Ediv -> Proven_idiv
                    | `Mod | `Emod -> Proven_imod
                  in
                  let temporary = ngensym ~source_name:"integer_result" ~source_type:(string_of_ctyp carrier) () in
                  iblock
                    (left_setup @ right_setup
                    @ [
                        idecl l carrier temporary;
                        icopy l (CL_id (temporary, carrier)) (V_call (represented_op, [left; right]));
                        icopy l result (V_id (temporary, carrier));
                        iclear ~loc:l carrier temporary;
                      ]
                    @ right_cleanup @ left_cleanup
                    )
              | Some _ | None -> instr
            )
        )
      | instr -> instr
    in
    let specialize_integer_primitive lifetime_ranges = function
      | I_aux (I_funcall (CR_one result, call, (id, tyargs), [left; right]), aux) as instr -> (
          let source_primitive = integer_primitive_name ctx id in
          let comparison = integer_comparison_name ctx id in
          let argument_intervals, result_interval, semantic_proofs =
            match call with
            | Call ((argument_intervals, result_interval), proofs) -> (argument_intervals, result_interval, proofs)
            | _ -> ([], None, [])
          in
          let callsite_lifetime index fallback =
            match List.nth_opt argument_intervals index |> Option.join with
            | Some (lower, upper) -> meet_integer_lifetime fallback (Lifetime_range (lower, upper))
            | None -> fallback
          in
          let left_lifetime = callsite_lifetime 0 (cval_integer_lifetime lifetime_ranges left) in
          let right_lifetime = callsite_lifetime 1 (cval_integer_lifetime lifetime_ranges right) in
          let left_lifetime, right_lifetime =
            match (source_primitive, left_lifetime, right_lifetime) with
            | Some `Sub, Lifetime_range (left_lower, left_upper), Lifetime_range (right_lower, right_upper)
              when Jib_semantics.has_argument_le ~left:1 ~right:0 semantic_proofs ->
                ( Lifetime_range (Big_int.max left_lower right_lower, left_upper),
                  Lifetime_range (right_lower, Big_int.min right_upper left_upper)
                )
            | _ -> (left_lifetime, right_lifetime)
          in
          let primitive =
            match source_primitive with
            | Some `Ediv -> (
                log_progress "euclidean-div function=%s left=%s right=%s" (string_of_id id)
                  (string_of_integer_interval (integer_lifetime_interval left_lifetime))
                  (string_of_integer_interval (integer_lifetime_interval right_lifetime));
                match lifetime_euclidean_nonnegative lifetime_div left_lifetime right_lifetime with
                | Lifetime_range _ -> Some `Div
                | Lifetime_bottom | Lifetime_top -> None
              )
            | Some `Emod -> (
                log_progress "euclidean-mod function=%s left=%s right=%s" (string_of_id id)
                  (string_of_integer_interval (integer_lifetime_interval left_lifetime))
                  (string_of_integer_interval (integer_lifetime_interval right_lifetime));
                match lifetime_euclidean_nonnegative lifetime_mod left_lifetime right_lifetime with
                | Lifetime_range _ -> Some `Mod
                | Lifetime_bottom | Lifetime_top -> None
              )
            | primitive -> primitive
          in
          let result_lifetime, carrier_lifetime =
            match primitive with
            | Some primitive ->
                let inferred_result = integer_primitive_operation_lifetime primitive left_lifetime right_lifetime in
                let result_lifetime =
                  match result_interval with
                  | Some (lower, upper) -> meet_integer_lifetime inferred_result (Lifetime_range (lower, upper))
                  | None -> inferred_result
                in
                let result_lifetime =
                  match C.integer_representation_bounds (clexp_ctyp result) with
                  | Some (lower, upper) when Jib_semantics.has_result_bounds ~lower ~upper semantic_proofs ->
                      meet_integer_lifetime result_lifetime (Lifetime_range (lower, upper))
                  | Some _ | None -> result_lifetime
                in
                let result_lifetime =
                  (* A subtrahend-not-above-minuend ordering proof implies the
                     exact difference is nonnegative.  Callers prove the
                     ordering on their own argument types, while the direct
                     result proof is attempted on the callee's freshened
                     signature return type (e.g. int('n - 'm)), whose
                     variables are never instantiated in the caller
                     environment; treat the ordering proof as result evidence
                     so guarded subtractions keep their nonnegative lower
                     bound. *)
                  match result_lifetime with
                  | Lifetime_range (lower, upper)
                    when primitive = `Sub
                         && (Jib_semantics.has_result_nonnegative semantic_proofs
                            || Jib_semantics.has_argument_le ~left:1 ~right:0 semantic_proofs
                            ) ->
                      Lifetime_range (Big_int.max Big_int.zero lower, upper)
                  | result -> result
                in
                ( result_lifetime,
                  join_integer_lifetime result_lifetime (join_integer_lifetime left_lifetime right_lifetime)
                )
            | None -> (Lifetime_top, Lifetime_top)
          in
          let comparison_carrier =
            represented_integer_lifetime ctx (join_integer_lifetime left_lifetime right_lifetime)
          in
          let constant_comparison =
            match comparison with
            | Some comparison -> constant_integer_comparison comparison left_lifetime right_lifetime
            | None -> None
          in
          let division_semantic_proofs carrier =
            match primitive with
            | Some (`Div | `Mod) ->
                let prove index lifetime value =
                  Jib_semantics.prove_argument_excludes_interval ~index ~interval:(integer_lifetime_interval lifetime)
                    ~value
                in
                let signed_exclusions =
                  match carrier with
                  | CT_fint width ->
                      [prove 0 left_lifetime (min_int width); prove 1 right_lifetime (Big_int.of_int (-1))]
                  | _ -> []
                in
                List.filter_map Fun.id (prove 1 right_lifetime Big_int.zero :: signed_exclusions) @ semantic_proofs
            | Some (`Add | `Sub | `Mul | `Ediv | `Emod) | None -> semantic_proofs
          in
          let l = snd aux in
          let promote carrier lifetime value =
            if ctyp_equal (cval_ctyp value) carrier then ([], value, [])
            else (
              match (proven_native_conversion carrier lifetime value, value) with
              | Some converted, _ -> ([], converted, [])
              | None, V_lit (VL_int literal, _) -> ([], V_lit (VL_int literal, carrier), [])
              | None, _ ->
                  let temporary = ngensym () in
                  ( [idecl l carrier temporary; icopy l (CL_id (temporary, carrier)) value],
                    V_id (temporary, carrier),
                    [iclear ~loc:l carrier temporary]
                  )
            )
          in
          let c_integer_promotion = function
            | CT_fint width when width < 32 -> Some (CT_fint 32)
            | CT_fuint width when width < 32 -> Some (CT_fint 32)
            | (CT_fint _ | CT_fuint _) as ctyp -> Some ctyp
            | _ -> None
          in
          let c_arithmetic_carrier left right =
            match (c_integer_promotion (cval_ctyp left), c_integer_promotion (cval_ctyp right)) with
            | Some (CT_fint left_width), Some (CT_fint right_width) -> Some (CT_fint (Int.max left_width right_width))
            | Some (CT_fuint left_width), Some (CT_fuint right_width) -> Some (CT_fuint (Int.max left_width right_width))
            | Some (CT_fint signed_width), Some (CT_fuint unsigned_width)
            | Some (CT_fuint unsigned_width), Some (CT_fint signed_width) ->
                if signed_width > unsigned_width then Some (CT_fint signed_width)
                else Some (CT_fuint (Int.max signed_width unsigned_width))
            | _ -> None
          in
          let exact_mixed_fixed_comparison left right =
            if ctyp_equal (cval_ctyp left) (cval_ctyp right) then false
            else (
              match (cval_ctyp left, cval_ctyp right, c_arithmetic_carrier left right) with
              | CT_fint _, CT_fint _, Some _ | CT_fuint _, CT_fuint _, Some _ -> true
              | CT_fint _, CT_fuint _, Some (CT_fint _) | CT_fuint _, CT_fint _, Some (CT_fint _) -> true
              | CT_fint _, CT_fuint _, Some (CT_fuint _) -> (
                  match left_lifetime with
                  | Lifetime_range (lower, _) -> Big_int.less_equal Big_int.zero lower
                  | Lifetime_bottom | Lifetime_top -> false
                )
              | CT_fuint _, CT_fint _, Some (CT_fuint _) -> (
                  match right_lifetime with
                  | Lifetime_range (lower, _) -> Big_int.less_equal Big_int.zero lower
                  | Lifetime_bottom | Lifetime_top -> false
                )
              | _ -> false
            )
          in
          let mixed_custom_comparison = mixed_custom_unsigned_representations left right in
          match (comparison, constant_comparison, comparison_carrier, mixed_custom_comparison) with
          | Some _, Some value, _, _ -> I_aux (I_copy (result, V_lit (VL_bool value, CT_bool)), aux)
          | Some op, None, Some _, Some (left, right) -> I_aux (I_copy (result, V_call (op, [left; right])), aux)
          | Some op, None, Some _, None when exact_mixed_fixed_comparison left right ->
              I_aux (I_copy (result, V_call (op, [left; right])), aux)
          | Some op, None, Some carrier, None ->
              let left_setup, left, left_cleanup = promote carrier left_lifetime left in
              let right_setup, right, right_cleanup = promote carrier right_lifetime right in
              iblock
                (left_setup @ right_setup
                @ [I_aux (I_copy (result, V_call (op, [left; right])), aux)]
                @ right_cleanup @ left_cleanup
                )
          | _ -> (
              match (primitive, represented_integer_lifetime ctx carrier_lifetime) with
              | Some primitive, Some carrier ->
                  let semantic_proofs = division_semantic_proofs carrier in
                  let division_is_defined =
                    match primitive with
                    | `Div | `Mod -> (
                        Jib_semantics.has_argument_excludes ~index:1 ~value:Big_int.zero semantic_proofs
                        &&
                        match carrier with
                        | CT_fint width ->
                            Jib_semantics.has_argument_excludes ~index:0 ~value:(min_int width) semantic_proofs
                            || Jib_semantics.has_argument_excludes ~index:1 ~value:(Big_int.of_int (-1)) semantic_proofs
                        | _ -> true
                      )
                    | `Add | `Sub | `Mul | `Ediv | `Emod -> true
                  in
                  if
                    (ctyp_equal (clexp_ctyp result) CT_lint && primitive <> `Div && primitive <> `Mod)
                    || not division_is_defined
                  then instr
                  else (
                    let custom_unsigned_carrier =
                      match carrier with
                      | CT_fint _ | CT_fuint _ -> false
                      | _ -> (
                          match C.integer_representation_bounds carrier with
                          | Some (lower, _) -> Big_int.equal lower Big_int.zero
                          | None -> false
                        )
                    in
                    let as_native_unsigned value =
                      match as_unsigned_representation value with
                      | Some value when match cval_ctyp value with CT_fuint _ -> true | _ -> false -> Some value
                      | Some _ | None -> None
                    in
                    let left, right, left_lifetime, right_lifetime =
                      match (primitive, as_native_unsigned left, ctyp_equal (cval_ctyp right) carrier) with
                      | (`Add | `Mul), Some left, true -> (right, left, right_lifetime, left_lifetime)
                      | _ -> (left, right, left_lifetime, right_lifetime)
                    in
                    let proven_mixed_operands =
                      if custom_unsigned_carrier then exact_mixed_unsigned_representations carrier left right else None
                    in
                    let result_carrier = represented_integer_lifetime ctx result_lifetime in
                    let power_of_two_operation =
                      match (primitive, left_lifetime, right_lifetime, carrier) with
                      | ( (`Div | `Mod),
                          Lifetime_range (left_lower, _),
                          Lifetime_range (right_lower, right_upper),
                          (CT_fint _ | CT_fuint _) )
                        when Big_int.less_equal Big_int.zero left_lower && Big_int.equal right_lower right_upper ->
                          Option.map
                            (fun exponent ->
                              match primitive with
                              | `Div -> Power_of_two_idiv exponent
                              | `Mod -> Power_of_two_imod exponent
                              | `Add | `Sub | `Mul | `Ediv | `Emod -> assert false
                            )
                            (power_of_two_width right_lower)
                      | _ -> None
                    in
                    let mixed_fixed_operation =
                      match (power_of_two_operation, primitive, result_carrier, c_arithmetic_carrier left right) with
                      | ( None,
                          ((`Div | `Mod) as primitive),
                          Some ((CT_fint _ | CT_fuint _) as result_ctyp),
                          Some ((CT_fint _ | CT_fuint _) as operation_ctyp) )
                        when not (ctyp_equal (cval_ctyp left) (cval_ctyp right)) ->
                          let conversion_is_exact =
                            match (cval_ctyp left, cval_ctyp right, operation_ctyp) with
                            | CT_fint _, CT_fint _, _ | CT_fuint _, CT_fuint _, _ -> true
                            | CT_fint _, CT_fuint _, CT_fint _ | CT_fuint _, CT_fint _, CT_fint _ -> true
                            | CT_fint _, CT_fuint _, CT_fuint _ -> (
                                match left_lifetime with
                                | Lifetime_range (lower, _) -> Big_int.less_equal Big_int.zero lower
                                | Lifetime_bottom | Lifetime_top -> false
                              )
                            | CT_fuint _, CT_fint _, CT_fuint _ -> (
                                match right_lifetime with
                                | Lifetime_range (lower, _) -> Big_int.less_equal Big_int.zero lower
                                | Lifetime_bottom | Lifetime_top -> false
                              )
                            | _ -> false
                          in
                          let argument_excludes index lifetime value =
                            Jib_semantics.has_argument_excludes ~index ~value semantic_proofs
                            || Option.is_some
                                 (Jib_semantics.prove_argument_excludes_interval ~index
                                    ~interval:(integer_lifetime_interval lifetime) ~value
                                 )
                          in
                          let operation_is_defined =
                            match operation_ctyp with
                            | CT_fint width ->
                                argument_excludes 0 left_lifetime (min_int width)
                                || argument_excludes 1 right_lifetime (Big_int.of_int (-1))
                            | CT_fuint _ -> true
                            | _ -> false
                          in
                          if conversion_is_exact && operation_is_defined then
                            Some
                              ( match primitive with
                              | `Div -> Mixed_proven_idiv (operation_ctyp, result_ctyp)
                              | `Mod -> Mixed_proven_imod (operation_ctyp, result_ctyp)
                              | `Add | `Sub | `Mul | `Ediv | `Emod -> assert false
                              )
                          else None
                      | _ -> None
                    in
                    let preserve_native_operands =
                      Option.is_some power_of_two_operation || Option.is_some mixed_fixed_operation
                    in
                    log_progress "primitive=%s carrier=%s result=%s left=%s(%s) right=%s(%s) preserve-mixed=%b"
                      (string_of_id id) (string_of_ctyp carrier)
                      (Option.fold ~none:"?" ~some:string_of_ctyp result_carrier)
                      (string_of_ctyp (cval_ctyp left))
                      (string_of_integer_interval (integer_lifetime_interval left_lifetime))
                      (string_of_ctyp (cval_ctyp right))
                      (string_of_integer_interval (integer_lifetime_interval right_lifetime))
                      (Option.is_some proven_mixed_operands || preserve_native_operands);
                    let promote lifetime value =
                      if ctyp_equal (cval_ctyp value) carrier then ([], value, [])
                      else (
                        match (proven_native_conversion carrier lifetime value, value) with
                        | Some converted, _ -> ([], converted, [])
                        | None, V_lit (VL_int literal, _) -> ([], V_lit (VL_int literal, carrier), [])
                        | None, _ ->
                            let temporary = ngensym () in
                            ( [idecl l carrier temporary; icopy l (CL_id (temporary, carrier)) value],
                              V_id (temporary, carrier),
                              [iclear ~loc:l carrier temporary]
                            )
                      )
                    in
                    let left_setup, left, left_cleanup =
                      match (preserve_native_operands, proven_mixed_operands) with
                      | true, _ -> ([], left, [])
                      | false, Some (left, _) -> ([], left, [])
                      | false, None -> promote left_lifetime left
                    in
                    let right_setup, right, right_cleanup =
                      match (preserve_native_operands, proven_mixed_operands) with
                      | true, _ -> ([], right, [])
                      | false, Some (_, right) -> ([], right, [])
                      | false, None when custom_unsigned_carrier -> (
                          match as_native_unsigned right with
                          | Some right -> ([], right, [])
                          | None -> promote right_lifetime right
                        )
                      | false, None -> promote right_lifetime right
                    in
                    let op =
                      match (primitive, carrier) with
                      | `Add, (CT_fint _ | CT_fuint _) -> Proven_iadd
                      | `Sub, (CT_fint _ | CT_fuint _) -> Proven_isub
                      | `Mul, (CT_fint _ | CT_fuint _) -> Proven_imul
                      | `Div, (CT_fint _ | CT_fuint _) -> Proven_idiv
                      | `Mod, (CT_fint _ | CT_fuint _) -> Proven_imod
                      | `Ediv, (CT_fint _ | CT_fuint _) -> Proven_idiv
                      | `Emod, (CT_fint _ | CT_fuint _) -> Proven_imod
                      | `Add, _ -> Iadd
                      | `Sub, _ -> Isub
                      | `Mul, _ -> Imul
                      | `Div, _ -> Idiv
                      | `Mod, _ -> Imod
                      | `Ediv, _ -> Idiv
                      | `Emod, _ -> Imod
                    in
                    let operation =
                      match (power_of_two_operation, mixed_fixed_operation) with
                      | Some op, _ -> V_call (op, [left])
                      | None, Some op -> V_call (op, [left; right])
                      | None, None -> V_call (op, [left; right])
                    in
                    let operation_result_carrier =
                      match (power_of_two_operation, mixed_fixed_operation, result_carrier) with
                      | Some _, _, Some result_carrier | None, Some _, Some result_carrier -> result_carrier
                      | _ -> carrier
                    in
                    let operation_instrs =
                      if ctyp_equal (clexp_ctyp result) operation_result_carrier then
                        [I_aux (I_copy (result, operation), aux)]
                      else (
                        let temporary =
                          ngensym ~source_name:"integer_result"
                            ~source_type:(string_of_ctyp operation_result_carrier)
                            ()
                        in
                        [
                          idecl l operation_result_carrier temporary;
                          icopy l (CL_id (temporary, operation_result_carrier)) operation;
                          icopy l result (V_id (temporary, operation_result_carrier));
                          iclear ~loc:l operation_result_carrier temporary;
                        ]
                      )
                    in
                    iblock (left_setup @ right_setup @ operation_instrs @ right_cleanup @ left_cleanup)
                  )
              | _ -> instr
            )
        )
      | instr -> instr
    in
    let restore_aggregate_field_representations =
      object
        inherit empty_jib_visitor

        method! vcval cval =
          match cval with
          | V_field (base, field, _) ->
              ChangeDoChildrenPost
                ( cval,
                  function
                  | V_field (base, field, _) ->
                      let _, field_ctyp = struct_fields (id_loc field) ctx (cval_ctyp base) in
                      V_field (base, field, field_ctyp field)
                  | cval -> cval
                )
          | _ -> DoChildren

        method! vclexp clexp =
          match clexp with
          | CL_field (base, field, _) ->
              ChangeDoChildrenPost
                ( clexp,
                  function
                  | CL_field (base, field, _) ->
                      let _, field_ctyp = struct_fields (id_loc field) ctx (clexp_ctyp base) in
                      CL_field (base, field, field_ctyp field)
                  | clexp -> clexp
                )
          | _ -> DoChildren
      end
    in
    (* A canonical function body can already contain values whose complete
       lifetime is finite even when the surrounding Sail helper deliberately
       keeps a generic mathematical-integer signature.  This commonly occurs
       when a native-width aggregate field is first bound to a local and then
       passed to a generic helper.  Rewrite those proved finite locals before
       discovering representation demands from the body's calls; otherwise
       the call is inspected as [sail_int] and the fixed-width representation
       is lost at precisely the function boundary specialization is intended
       to preserve.

       Parameters and the return register are intentionally protected here.
       Their representations are part of the canonical ABI and may change
       only in a demanded clone.  Recursive calls are likewise left alone in
       the canonical body: once an external call demands a clone, that clone's
       existing [current_specialization] handling gives its recursive edge a
       stable target without recursively generating demands. *)
    let specialize_original_function_body = function
      | CDEF_aux (CDEF_fundef (id, heap_return, params, body), fundef_annot) as cdef -> (
          match Bindings.find_opt id valspecs with
          | Some ([], param_ctyps, ret_ctyp, None, _) when List.compare_lengths params param_ctyps = 0 ->
              let parameter_intervals =
                List.map (fun ctyp -> integer_lifetime_interval (ctyp_integer_lifetime ctyp)) param_ctyps
              in
              let lifetime_ranges, lifetime_writes =
                infer_integer_lifetimes ctx id params param_ctyps parameter_intervals body
              in
              let path_lifetime_ranges, path_storage_ranges, path_decisions =
                infer_path_integer_lifetimes ~call_predicate_fact ctx id lifetime_ranges body
              in
              let lifetime_ranges = path_sensitive_storage_ranges lifetime_ranges path_storage_ranges in
              let protected = NameSet.of_list (return :: params) in
              let replacements =
                NameMap.fold
                  (fun name semantic replacements ->
                    if NameSet.mem name protected then replacements
                    else (
                      match (semantic, NameMap.find_opt name lifetime_ranges) with
                      | CT_lint, Some lifetime -> (
                          match represented_integer_lifetime ctx lifetime with
                          | Some represented -> NameMap.add name represented replacements
                          | None -> replacements
                        )
                      | _ -> replacements
                    )
                  )
                  lifetime_writes NameMap.empty
              in
              let visitor = new specialize_parameter_representations replacements ret_ctyp ret_ctyp in
              let rewrite_non_recursive_call lifetime_ranges = function
                | I_aux (I_funcall (_, Call _, (callee, []), _), _) as instr when Id.compare id callee = 0 -> instr
                | instr -> rewrite_call ~lifetime_ranges instr
              in
              let body =
                prune_proved_unreachable path_lifetime_ranges path_decisions body
                |> List.map (visit_instr visitor)
                |> List.map (visit_instr restore_aggregate_field_representations)
                |> rewrite_wrapping_arithmetic
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_integer_conversion
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_bitvector_shift
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_bitvector_slice
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_fixed_vector_access
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_structural_integer_primitive
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges specialize_integer_primitive)
                (* Structural and primitive specialization can introduce a
                   fresh wide-to-narrow copy.  Mark that generated boundary
                   only after it exists so the backend can distinguish a
                   proved projection from an unchecked assumption. *)
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_integer_conversion
                     )
                |> remove_unused_literal_temporaries
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges rewrite_non_recursive_call)
              in
              if not (NameMap.is_empty replacements) then
                log_progress "specialized original body function=%s locals=%d" (string_of_id id)
                  (NameMap.cardinal replacements);
              CDEF_aux (CDEF_fundef (id, heap_return, params, body), fundef_annot)
          | _ -> cdef
        )
      | cdef -> cdef
    in
    let cdefs = List.map specialize_original_function_body cdefs in
    while not (Queue.is_empty pending) do
      let id, signature = Queue.take pending in
      let demand = RepresentationDemandMap.find signature (Bindings.find id !demanded) in
      demand.RepresentationDemand.queued := false;
      let specialized_id = demand.RepresentationDemand.specialized_id in
      let actual_ctyps = demand.RepresentationDemand.actual_ctyps in
      let actual_ret_ctyp = demand.RepresentationDemand.actual_ret_ctyp in
      let lifetime_ranges = !(demand.RepresentationDemand.lifetime_ranges) in
      let path_lifetime_ranges = !(demand.RepresentationDemand.path_lifetime_ranges) in
      let path_decisions = !(demand.RepresentationDemand.path_decisions) in
      let lifetime_writes = demand.RepresentationDemand.lifetime_writes in
      incr processed_demands;
      let clone_started_at = Sys.time () in
      log_progress "processing=%d/%d queued=%d function=%s" !processed_demands !total_demands (Queue.length pending)
        (string_of_id id);
      match (Bindings.find id valspecs, Bindings.find id fundefs) with
      | ([], param_ctyps, ret_ctyp, None, val_annot), (heap_return, params, body, fundef_annot) ->
          if List.compare_lengths params actual_ctyps <> 0 then
            Reporting.unreachable (id_loc id) __POS__ ("Function parameters do not match valspec for " ^ string_of_id id);
          let replacements =
            List.fold_left2
              (fun replacements (param, semantic) represented ->
                if ctyp_equal semantic represented then replacements else NameMap.add param represented replacements
              )
              NameMap.empty (List.combine params param_ctyps) actual_ctyps
          in
          log_progress "inferred function=%s values=%d elapsed=%.2fs" (string_of_id id)
            (NameMap.cardinal lifetime_ranges)
            (Sys.time () -. clone_started_at);
          let signature_owned = NameSet.of_list (return :: params) in
          let replacements =
            NameMap.fold
              (fun name semantic replacements ->
                if NameSet.mem name signature_owned then replacements
                else (
                  match (semantic, NameMap.find_opt name lifetime_ranges) with
                  | CT_lint, Some lifetime -> (
                      match represented_integer_lifetime ctx lifetime with
                      | Some represented ->
                          log_progress "value function=%s name=%s lifetime=%s represented=%s" (string_of_id id)
                            (string_of_name ~zencode:false name)
                            (string_of_integer_interval (integer_lifetime_interval lifetime))
                            (string_of_ctyp represented);
                          NameMap.add name represented replacements
                      | None ->
                          log_progress "value function=%s name=%s lifetime=%s represented=unbounded" (string_of_id id)
                            (string_of_name ~zencode:false name)
                            (string_of_integer_interval (integer_lifetime_interval lifetime));
                          replacements
                    )
                  | _ -> replacements
                )
              )
              lifetime_writes replacements
          in
          let replacements =
            if ctyp_equal ret_ctyp actual_ret_ctyp then replacements
            else NameMap.add return actual_ret_ctyp replacements
          in
          let visitor = new specialize_parameter_representations replacements ret_ctyp actual_ret_ctyp in
          let body =
            (* Spliced overrides also win in representation clones; see the
               original-body selection above. *)
            match
              if Option.is_some (get_def_attribute "spliced" fundef_annot) then None
              else C.specialized_function_external id actual_ctyps actual_ret_ctyp
            with
            | Some external_id ->
                let l = id_loc id in
                let args = List.map2 (fun param ctyp -> V_id (param, ctyp)) params actual_ctyps in
                let call =
                  match ifuncall l (CL_id (return, actual_ret_ctyp)) (external_id, []) args with
                  | I_aux (I_funcall (creturn, _, fn, call_args), aux) ->
                      I_aux (I_funcall (creturn, Extern actual_ret_ctyp, fn, call_args), aux)
                  | _ -> assert false
                in
                [call; iend l]
            | None ->
                prune_proved_unreachable path_lifetime_ranges path_decisions body
                |> List.map (visit_instr visitor)
                |> List.map (visit_instr restore_aggregate_field_representations)
                |> rewrite_wrapping_arithmetic
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_integer_conversion
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_bitvector_shift
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_bitvector_slice
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_fixed_vector_access
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_structural_integer_primitive
                     )
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges specialize_integer_primitive)
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges
                        specialize_proven_integer_conversion
                     )
                |> remove_unused_literal_temporaries
                |> List.map
                     (map_instr_with_lifetime_ranges lifetime_ranges path_lifetime_ranges (fun lifetime_ranges ->
                          rewrite_call ~lifetime_ranges
                            ~current_specialization:
                              (id, specialized_id, actual_ctyps, actual_ret_ctyp, !(demand.RepresentationDemand.bounds))
                      )
                     )
          in
          let specialized_val =
            CDEF_aux (CDEF_val (specialized_id, [], actual_ctyps, actual_ret_ctyp, None), val_annot)
          in
          let specialized_fundef = CDEF_aux (CDEF_fundef (specialized_id, heap_return, params, body), fundef_annot) in
          let calls = ref [] in
          let conversions = ref [] in
          let record_conversion source destination proven =
            if not (ctyp_equal source destination) then conversions := (source, destination, proven) :: !conversions
          in
          let conversion_visitor =
            object
              inherit empty_jib_visitor

              method! vcval =
                function
                | V_call (Proven_narrow destination, [source]) ->
                    record_conversion (cval_ctyp source) destination true;
                    DoChildren
                | _ -> DoChildren
            end
          in
          List.iter (fun instr -> ignore (visit_instr conversion_visitor instr)) body;
          List.iter
            (iter_instr (function
              | I_aux (I_funcall (creturn, call_kind, (callee, ctyps), _), _) ->
                  calls :=
                    ( callee,
                      ctyps,
                      creturn_ctyp creturn,
                      ctx_is_extern callee ctx || match call_kind with Extern _ -> true | Call _ -> false
                    )
                    :: !calls
              | I_aux (I_copy (destination, value), _) ->
                  record_conversion (cval_ctyp value) (clexp_ctyp destination) false
              | I_aux (I_init (destination, _, Init_cval value), _) | I_aux (I_reinit (destination, _, value), _) ->
                  record_conversion (cval_ctyp value) destination false
              | _ -> ()
              ))
            body;
          let argument_bounds, result_bound = !(demand.RepresentationDemand.bounds) in
          let trace =
            {
              source_id = id;
              specialized_id;
              source_location = fundef_annot.loc;
              semantic_parameters = param_ctyps;
              represented_parameters = actual_ctyps;
              semantic_result = ret_ctyp;
              represented_result = actual_ret_ctyp;
              argument_bounds;
              result_bound;
              calls = List.rev !calls;
              conversions = List.rev !conversions;
              recursive =
                List.exists
                  (fun (callee, _, _, is_extern) -> (not is_extern) && Id.compare callee specialized_id = 0)
                  !calls;
            }
          in
          representation_specializations :=
            trace
            :: List.filter
                 (fun prior -> Id.compare prior.specialized_id specialized_id <> 0)
                 !representation_specializations;
          generated := Bindings.add specialized_id (specialized_val, specialized_fundef) !generated;
          specialized_ctx :=
            {
              !specialized_ctx with
              valspecs =
                Bindings.add specialized_id
                  (None, actual_ctyps, actual_ret_ctyp, uannot_of_def_annot val_annot)
                  !specialized_ctx.valspecs;
            };
          log_progress "generated function=%s elapsed=%.2fs queued=%d" (string_of_id id)
            (Sys.time () -. clone_started_at)
            (Queue.length pending)
      | _ -> Reporting.unreachable (id_loc id) __POS__ "Invalid representation-specialization target"
    done;
    (* Top-level singleton [let] bindings are immutable, so their exact value
       is also their complete lifetime and may select a native representation.
       Preserve CT_lint bindings and initializer temporaries for ordinary
       builds: an explicit unbounded result type remains the constant's storage
       contract, even when this particular initializer happens to be small.
       A specializing backend may instead use the complete immutable lifetime
       to represent an inferred [int] singleton natively.
       Do not apply this to registers: their initializer is not their complete
       lifecycle. *)
    let top_level_representations = ref NameMap.empty in
    let specialize_top_level_let = function
      | CDEF_aux (CDEF_let (index, bindings, body), def_annot) ->
          let owner = match bindings with (id, _) :: _ -> id | [] -> mk_id "top_level_let" in
          let lifetime_ranges, lifetime_writes = infer_integer_lifetimes ctx owner [] [] [] body in
          let declared_replacements =
            List.fold_left
              (fun replacements (id, represented) ->
                let name = name id in
                match NameMap.find_opt name lifetime_writes with
                | Some semantic
                  when (not (ctyp_equal semantic represented)) && C.representation_refines ~semantic ~represented ->
                    NameMap.add name represented replacements
                | Some _ | None -> replacements
              )
              NameMap.empty bindings
          in
          let replacements =
            NameMap.fold
              (fun name semantic replacements ->
                match (semantic, NameMap.find_opt name lifetime_ranges) with
                | (CT_constant _ | CT_lint), Some lifetime when (not (ctyp_equal semantic CT_lint)) || C.specialize_c
                  -> (
                    match represented_integer_lifetime ctx lifetime with
                    | Some represented ->
                        log_progress "top-level-let value=%s semantic=%s lifetime=%s represented=%s"
                          (string_of_name ~zencode:false name) (string_of_ctyp semantic)
                          (string_of_integer_interval (integer_lifetime_interval lifetime))
                          (string_of_ctyp represented);
                        NameMap.add name represented replacements
                    | None ->
                        log_progress "top-level-let value=%s semantic=%s lifetime=%s represented=unbounded"
                          (string_of_name ~zencode:false name) (string_of_ctyp semantic)
                          (string_of_integer_interval (integer_lifetime_interval lifetime));
                        replacements
                  )
                | _ -> replacements
              )
              lifetime_writes declared_replacements
          in
          top_level_representations :=
            NameMap.fold
              (fun name represented replacements -> NameMap.add name represented replacements)
              replacements !top_level_representations;
          let represented_binding (id, ctyp) =
            match NameMap.find_opt (name id) replacements with
            | Some represented -> (id, represented)
            | None -> (id, ctyp)
          in
          let visitor = new specialize_parameter_representations replacements CT_unit CT_unit in
          let represent_assigned_literal represented = function
            | V_lit (VL_int literal, CT_lint) as value -> (
                match C.integer_representation_bounds represented with
                | Some (lower, upper) when Big_int.less_equal lower literal && Big_int.less_equal literal upper ->
                    V_lit (VL_int literal, represented)
                | _ -> value
              )
            | value -> value
          in
          let specialize_literal_assignment = function
            | I_aux (I_init (represented, name, Init_cval value), aux) ->
                I_aux (I_init (represented, name, Init_cval (represent_assigned_literal represented value)), aux)
            | I_aux (I_reinit (represented, name, value), aux) ->
                I_aux (I_reinit (represented, name, represent_assigned_literal represented value), aux)
            | I_aux (I_copy (destination, value), aux) ->
                I_aux (I_copy (destination, represent_assigned_literal (clexp_ctyp destination) value), aux)
            | instr -> instr
          in
          let body =
            List.map (visit_instr visitor) body
            |> List.map (visit_instr restore_aggregate_field_representations)
            |> List.map (map_instr (specialize_structural_integer_primitive lifetime_ranges))
            |> List.map (map_instr specialize_literal_assignment)
            |> List.map (map_instr (specialize_integer_primitive lifetime_ranges))
            |> List.map (map_instr (specialize_proven_integer_conversion lifetime_ranges))
            |> List.map (map_instr (specialize_proven_fixed_vector_access lifetime_ranges))
          in
          CDEF_aux (CDEF_let (index, List.map represented_binding bindings, body), def_annot)
      | cdef -> cdef
    in
    let cdefs = List.map specialize_top_level_let cdefs in
    (* Rewriting a top-level immutable binding's storage is only half of the
       representation change. References compiled before this pass still
       carry the binding's semantic [CT_lint] annotation. Propagate the proved
       representation through those references so ordinary copy lowering can
       add a conversion only at a genuinely managed consumer boundary. Without
       this pass a specializing non-strict build emits, for example, a
       [COPY(sail_int)] whose source is a native [uint64_t]. *)
    let top_level_representation_visitor =
      object
        inherit empty_jib_visitor

        method! vctyp _ = SkipChildren

        method! vcval =
          function
          | V_id (name, _) as cval -> (
              match NameMap.find_opt name !top_level_representations with
              | Some represented -> ChangeTo (V_id (name, represented))
              | None -> ChangeTo cval
            )
          | _ -> DoChildren

        method! vclexp =
          function
          | CL_id (name, _) as clexp -> (
              match NameMap.find_opt name !top_level_representations with
              | Some represented -> ChangeTo (CL_id (name, represented))
              | None -> ChangeTo clexp
            )
          | CL_rmw (read, write, _) as clexp -> (
              match
                (NameMap.find_opt read !top_level_representations, NameMap.find_opt write !top_level_representations)
              with
              | Some read_ctyp, Some write_ctyp when not (ctyp_equal read_ctyp write_ctyp) ->
                  Reporting.unreachable Parse_ast.Unknown __POS__
                    "Read-modify-write names have different top-level representations"
              | Some represented, _ | _, Some represented -> ChangeTo (CL_rmw (read, write, represented))
              | None, None -> ChangeTo clexp
            )
          | _ -> DoChildren
      end
    in
    let resolve_generic_proven_arithmetic =
      let ordinary_math_call result ordinary tyargs left right aux =
        let l = snd aux in
        let promote value =
          if ctyp_equal (cval_ctyp value) CT_lint then ([], value, [])
          else (
            let temporary = ngensym ~source_name:"integer_operand" ~source_type:(string_of_ctyp CT_lint) () in
            ( [idecl l CT_lint temporary; icopy l (CL_id (temporary, CT_lint)) value],
              V_id (temporary, CT_lint),
              [iclear ~loc:l CT_lint temporary]
            )
          )
        in
        let left_setup, left, left_cleanup = promote left in
        let right_setup, right, right_cleanup = promote right in
        let result_setup, call_result, result_cleanup =
          if ctyp_equal (clexp_ctyp result) CT_lint then ([], result, [])
          else (
            let temporary = ngensym ~source_name:"integer_result" ~source_type:(string_of_ctyp CT_lint) () in
            ( [idecl l CT_lint temporary],
              CL_id (temporary, CT_lint),
              [icopy l result (V_id (temporary, CT_lint)); iclear ~loc:l CT_lint temporary]
            )
          )
        in
        iblock
          (left_setup @ right_setup @ result_setup
          @ [I_aux (I_funcall (CR_one call_result, Extern CT_lint, (mk_id ordinary, tyargs), [left; right]), aux)]
          @ result_cleanup @ right_cleanup @ left_cleanup
          )
      in
      function
      | I_aux (I_funcall (CR_one result, Call (_, semantic_proofs), (id, tyargs), [left; right]), aux)
        when String.starts_with ~prefix:"__sail_proven_native_" (string_of_id id) -> (
          let represented = clexp_ctyp result in
          let l = snd aux in
          let value_fits index value lower upper =
            match value with
            | V_lit (VL_int literal, _) -> Big_int.less_equal lower literal && Big_int.less_equal literal upper
            | _ -> (
                match C.integer_representation_bounds (cval_ctyp value) with
                | Some (actual_lower, actual_upper) ->
                    Big_int.less_equal lower actual_lower && Big_int.less_equal actual_upper upper
                | None -> Jib_semantics.has_argument_bounds ~index ~lower ~upper semantic_proofs
              )
          in
          match C.integer_representation_bounds represented with
          | Some (lower, upper)
            when value_fits 0 left lower upper && value_fits 1 right lower upper
                 &&
                 let operation_is_proved =
                   match string_of_id id with
                   | "__sail_proven_native_add" | "__sail_proven_native_sub" | "__sail_proven_native_mul" ->
                       Jib_semantics.has_result_bounds ~lower ~upper semantic_proofs
                   | "__sail_proven_native_div" | "__sail_proven_native_mod" -> (
                       Jib_semantics.has_argument_excludes ~index:1 ~value:Big_int.zero semantic_proofs
                       &&
                       match represented with
                       | CT_fint width ->
                           Jib_semantics.has_argument_excludes ~index:0 ~value:(min_int width) semantic_proofs
                           || Jib_semantics.has_argument_excludes ~index:1 ~value:(Big_int.of_int (-1)) semantic_proofs
                       | _ -> true
                     )
                   | _ -> false
                 in
                 operation_is_proved ->
              (* The semantic web may reject a larger rewrite (for example a
                 non-power-of-two modulus) without invalidating the exact
                 native arithmetic proof carried by this call. Consume that
                 proof here, after web selection, so its marker cannot fall
                 back to sail_int merely because it deliberately survived the
                 earlier primitive-specialization pass. *)
              let promote value =
                if ctyp_equal (cval_ctyp value) represented then ([], value, [])
                else (
                  match value with
                  | V_lit (VL_int literal, _) -> ([], V_lit (VL_int literal, represented), [])
                  | _ ->
                      let temporary =
                        ngensym ~source_name:"integer_operand" ~source_type:(string_of_ctyp represented) ()
                      in
                      ( [idecl l represented temporary; icopy l (CL_id (temporary, represented)) value],
                        V_id (temporary, represented),
                        [iclear ~loc:l represented temporary]
                      )
                )
              in
              let fixed = match represented with CT_fint _ | CT_fuint _ -> true | _ -> false in
              let proven_mixed_operands = if fixed then None else mixed_custom_unsigned_representations left right in
              let left_setup, left, left_cleanup =
                match proven_mixed_operands with Some (left, _) -> ([], left, []) | None -> promote left
              in
              let right_setup, right, right_cleanup =
                match proven_mixed_operands with Some (_, right) -> ([], right, []) | None -> promote right
              in
              let operation =
                match (string_of_id id, fixed) with
                | "__sail_proven_native_add", true -> Proven_iadd
                | "__sail_proven_native_sub", true -> Proven_isub
                | "__sail_proven_native_mul", true -> Proven_imul
                | "__sail_proven_native_div", true -> Proven_idiv
                | "__sail_proven_native_mod", true -> Proven_imod
                | "__sail_proven_native_add", false -> Iadd
                | "__sail_proven_native_sub", false -> Isub
                | "__sail_proven_native_mul", false -> Imul
                | "__sail_proven_native_div", false -> Idiv
                | "__sail_proven_native_mod", false -> Imod
                | _ -> assert false
              in
              iblock
                (left_setup @ right_setup
                @ [I_aux (I_copy (result, V_call (operation, [left; right])), aux)]
                @ right_cleanup @ left_cleanup
                )
          | Some _ | None ->
              let ordinary =
                match string_of_id id with
                | "__sail_proven_native_add" -> "add_int"
                | "__sail_proven_native_sub" -> "sub_int"
                | "__sail_proven_native_mul" -> "mult_int"
                | "__sail_proven_native_div" -> "tdiv_int"
                | "__sail_proven_native_mod" -> "tmod_int"
                | _ -> assert false
              in
              ordinary_math_call result ordinary tyargs left right aux
        )
      | I_aux (I_funcall (_, Call _, (id, _), _), (_, l))
        when String.starts_with ~prefix:"__sail_proven_native_" (string_of_id id) ->
          Reporting.unreachable l __POS__ ("Malformed proven native arithmetic marker " ^ string_of_id id)
      | instr -> instr
    in
    let generated =
      Bindings.fold (fun _ (valspec, fundef) definitions -> fundef :: valspec :: definitions) !generated [] |> List.rev
    in
    log_progress "semantic-web selected=%d rejected-representations=%d" !wrapping_selected !wrapping_rejected;
    log_progress "complete clones=%d generated-definitions=%d" !total_demands (List.length generated);
    let cdefs = visit_cdefs top_level_representation_visitor (cdefs @ generated) in
    (* Resolve arithmetic proof markers only after every demanded clone has
       been generated and the final representations have propagated through
       those bodies.  Resolving first can select scalar [Proven_*] arithmetic
       and then have a def/call-graph specialization replace its operands with
       a wide value carrier such as [c_repr_u128].  It also leaves markers in
       newly generated clones unresolved.  At this point the selected carrier
       is definitive, so fixed C integers use [Proven_*] while wide plain-value
       carriers use their ordinary allocation-free helper operations. *)
    let cdefs = List.map (cdef_map_instr resolve_generic_proven_arithmetic) cdefs in
    (* A demanded clone replaces calls to the generic body, but the original
       definition was previously left in the output even when no reachable
       caller remained.  Besides carrying dead GMP code, that defeats
       [--c-require-bounded-int]: the deliberately generic implementation has
       mathematical-integer parameters, whereas every reachable clone has a
       proved concrete representation.

       Recompute reachability after call rewriting and remove only demanded
       originals that are no longer reachable.  Explicit compiler roots and
       calls made from top-level initializer blocks remain roots, so an
       exported or otherwise unspecialized generic implementation is kept. *)
    let demanded_ids = Bindings.fold (fun id _ ids -> IdSet.add id ids) !demanded IdSet.empty in
    let roots =
      List.fold_left (fun roots id -> IdGraphNS.add id roots) IdGraphNS.empty (Specialize.get_initial_calls ())
    in
    (* Every generated clone remains in the emitted translation unit, even
       when demand merging leaves it without a reachable caller.  Treat those
       emitted bodies as roots while deciding whether a canonical fallback is
       still required; otherwise an orphaned clone can retain a call to an
       original which this pass removes, leaving an undefined link symbol. *)
    let roots =
      List.fold_left
        (fun roots -> function CDEF_aux (CDEF_fundef (id, _, _, _), _) -> IdGraphNS.add id roots | _ -> roots)
        roots generated
    in
    let roots = ref roots in
    let add_top_level_calls = function
      | CDEF_aux
          ( (CDEF_register (_, _, instrs) | CDEF_let (_, _, instrs) | CDEF_startup (_, instrs) | CDEF_finish (_, instrs)),
            _
          ) ->
          List.iter
            (iter_instr (function
              | I_aux (I_funcall (_, _, (call, _), _), _) -> roots := IdGraphNS.add call !roots
              | _ -> ()
              ))
            instrs
      | _ -> ()
    in
    List.iter add_top_level_calls cdefs;
    let reachable = IdGraph.reachable !roots IdGraphNS.empty (callgraph cdefs) in
    let removed = IdSet.filter (fun id -> not (IdGraphNS.mem id reachable)) demanded_ids in
    if debug_demands then
      List.iter
        (function
          | CDEF_aux (CDEF_fundef (caller, _, _, instrs), _) when IdGraphNS.mem caller reachable ->
              List.iter
                (iter_instr (function
                  | I_aux (I_funcall (_, call_kind, (callee, _), args), _)
                    when IdSet.mem callee demanded_ids && not (IdSet.mem callee removed) ->
                      let bounds =
                        match call_kind with Call (bounds, _) -> string_of_call_bounds bounds | Extern _ -> "extern"
                      in
                      log_progress "retained generic function=%s caller=%s ctypes=[%s] %s" (string_of_id callee)
                        (string_of_id caller)
                        (Util.string_of_list "," (fun argument -> string_of_ctyp (cval_ctyp argument)) args)
                        bounds
                  | _ -> ()
                  ))
                instrs
          | _ -> ()
          )
        cdefs;
    let cdefs =
      List.filter
        (function
          | CDEF_aux (CDEF_fundef (id, _, _, _), _) when IdSet.mem id removed -> false
          | CDEF_aux (CDEF_val (id, _, _, _, _), _) when IdSet.mem id removed -> false
          | _ -> true
          )
        cdefs
    in
    IdSet.iter (fun id -> log_progress "removed unreachable generic function=%s" (string_of_id id)) removed;
    (cdefs, !specialized_ctx)

  let contains_struct id cdef =
    cdef_has_ctyp (ctyp_has (function CT_struct (id', _) -> Id.compare id id' = 0 | _ -> false)) cdef

  let contains_variant id cdef =
    cdef_has_ctyp (ctyp_has (function CT_variant (id', _) -> Id.compare id id' = 0 | _ -> false)) cdef

  class fix_variants_visitor ctx typ_id =
    object
      inherit empty_jib_visitor

      method! vctyp =
        function
        | CT_variant (id, args) when Id.compare typ_id id = 0 -> ChangeTo (CT_variant (mangle_mono_id id ctx args, []))
        | CT_struct (id, args) when Id.compare typ_id id = 0 -> ChangeTo (CT_struct (mangle_mono_id id ctx args, []))
        | _ -> DoChildren
    end

  class specialize_constructor_visitor instantiations ctx ctor_id =
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren
      method! vclexp _ = SkipChildren

      method! vcval =
        function
        | V_ctor_kind (cval, (id, unifiers)) when Id.compare id ctor_id = 0 ->
            change_do_children (V_ctor_kind (cval, (mangle_mono_id id ctx unifiers, [])))
        | V_ctor_unwrap (cval, (id, unifiers), ctor_ctyp) when Id.compare id ctor_id = 0 ->
            change_do_children (V_ctor_unwrap (cval, (mangle_mono_id id ctx unifiers, []), ctor_ctyp))
        | _ -> DoChildren

      method! vinstr =
        function
        | I_aux (I_funcall (clexp, extern, (id, ctyp_args), args), aux) when Id.compare id ctor_id = 0 ->
            instantiations := CTListSet.add ctyp_args !instantiations;
            I_aux (I_funcall (clexp, extern, (mangle_mono_id id ctx ctyp_args, []), args), aux) |> change_do_children
        | _ -> DoChildren
    end

  class specialize_field_visitor instantiations ctx struct_id =
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren
      method! vclexp _ = SkipChildren
      method! vcval _ = SkipChildren

      method! vinstr =
        function
        | I_aux (I_decl (CT_struct (struct_id', args), _), (_, l)) when Id.compare struct_id struct_id' = 0 ->
            instantiations := CTListSet.add args !instantiations;
            DoChildren
        | _ -> DoChildren
    end

  class scan_variant_visitor instantiations ctx var_id =
    object
      inherit empty_jib_visitor

      method! vctyp =
        function
        | CT_variant (var_id', args) when Id.compare var_id var_id' = 0 ->
            instantiations := CTListSet.add args !instantiations;
            DoChildren
        | _ -> DoChildren
    end

  let rec specialize_variants ctx prior =
    let instantiations = ref CTListSet.empty in
    let fix_variants ctx var_id = visit_ctyp (new fix_variants_visitor ctx var_id :> common_visitor) in

    let specialize_constructor ctx ctor_id =
      visit_cdefs (new specialize_constructor_visitor instantiations ctx ctor_id)
    in

    let specialize_field ctx struct_id = visit_cdefs (new specialize_field_visitor instantiations ctx struct_id) in

    let mangled_pragma orig_id mangled_id =
      CDEF_aux
        ( CDEF_pragma
            ("mangled", Util.zencode_string (string_of_id orig_id) ^ " " ^ Util.zencode_string (string_of_id mangled_id)),
          mk_def_annot (gen_loc (id_loc orig_id)) ()
        )
    in

    function
    | CDEF_aux (CDEF_type (CTD_variant (var_id, params, ctors)), def_annot) :: cdefs when not (Util.list_empty params)
      ->
        let _ = visit_cdefs (new scan_variant_visitor instantiations ctx var_id) prior in
        let _ = visit_cdefs (new scan_variant_visitor instantiations ctx var_id) cdefs in

        let cdefs =
          List.fold_left (fun cdefs (ctor_id, ctyp) -> specialize_constructor ctx ctor_id cdefs) cdefs ctors
        in

        let monomorphized_variants =
          List.map
            (fun inst ->
              let substs = KBindings.of_seq (List.map2 (fun x y -> (x, y)) params inst |> List.to_seq) in
              ( mangle_mono_id var_id ctx inst,
                List.map
                  (fun (ctor_id, ctyp) ->
                    (mangle_mono_id ctor_id ctx inst, fix_variants ctx var_id (subst_poly substs ctyp))
                  )
                  ctors
              )
            )
            (CTListSet.elements !instantiations)
        in
        let ctx =
          List.fold_left
            (fun ctx (id, ctors) ->
              { ctx with variants = Bindings.add id ([], Bindings.of_seq (List.to_seq ctors)) ctx.variants }
            )
            ctx monomorphized_variants
        in
        let mangled_ctors =
          List.map
            (fun (_, monomorphized_ctors) ->
              List.map2
                (fun (ctor_id, _) (monomorphized_id, _) -> mangled_pragma ctor_id monomorphized_id)
                ctors monomorphized_ctors
            )
            monomorphized_variants
          |> List.concat
        in

        let prior = Util.map_if (contains_variant var_id) (cdef_map_ctyp (fix_variants ctx var_id)) prior in
        let cdefs = Util.map_if (contains_variant var_id) (cdef_map_ctyp (fix_variants ctx var_id)) cdefs in

        let ctx = ctx_map_ctyps (fix_variants ctx var_id) ctx in
        let ctx = { ctx with variants = Bindings.remove var_id ctx.variants } in

        specialize_variants ctx
          (List.concat
             (List.map
                (fun (id, ctors) ->
                  [CDEF_aux (CDEF_type (CTD_variant (id, [], ctors)), def_annot); mangled_pragma var_id id]
                )
                monomorphized_variants
             )
          @ mangled_ctors @ prior
          )
          cdefs
    | CDEF_aux (CDEF_type (CTD_struct (struct_id, params, fields)), def_annot) :: cdefs when not (Util.list_empty params)
      ->
        let _ = specialize_field ctx struct_id cdefs in
        let monomorphized_structs =
          List.map
            (fun inst ->
              let substs = List.map2 (fun x y -> (x, y)) params inst |> List.to_seq |> KBindings.of_seq in
              ( mangle_mono_id struct_id ctx inst,
                List.map
                  (fun (field_id, ctyp) -> (field_id, fix_variants ctx struct_id (subst_poly substs ctyp)))
                  fields
              )
            )
            (CTListSet.elements !instantiations)
        in
        let mangled_fields =
          List.map
            (fun (_, monomorphized_fields) ->
              List.map2
                (fun (field_id, _) (monomorphized_id, _) -> mangled_pragma field_id monomorphized_id)
                fields monomorphized_fields
            )
            monomorphized_structs
          |> List.concat
        in

        let prior = Util.map_if (contains_struct struct_id) (cdef_map_ctyp (fix_variants ctx struct_id)) prior in
        let cdefs = Util.map_if (contains_struct struct_id) (cdef_map_ctyp (fix_variants ctx struct_id)) cdefs in
        let ctx = ctx_map_ctyps (fix_variants ctx struct_id) ctx in

        let ctx =
          List.fold_left
            (fun ctx (id, fields) ->
              { ctx with records = Bindings.add id ([], Bindings.of_seq (List.to_seq fields)) ctx.records }
            )
            ctx monomorphized_structs
        in
        let ctx = { ctx with records = Bindings.remove struct_id ctx.records } in

        specialize_variants ctx
          (List.concat
             (List.map
                (fun (id, fields) ->
                  [CDEF_aux (CDEF_type (CTD_struct (id, [], fields)), def_annot); mangled_pragma struct_id id]
                )
                monomorphized_structs
             )
          @ mangled_fields @ prior
          )
          cdefs
    | cdef :: cdefs -> specialize_variants ctx (cdef :: prior) cdefs
    | [] -> (List.rev prior, ctx)

  let make_calls_precise ctx cdefs =
    let constructor_types = ref Bindings.empty in

    let get_function_typ id =
      match Bindings.find_opt id ctx.valspecs with
      | None -> Bindings.find_opt id !constructor_types
      | Some (_, param_ctyps, ret_ctyp, _) -> Some (param_ctyps, ret_ctyp)
    in

    let precise_call call tail =
      match call with
      | I_aux (I_funcall (CR_one clexp, extern_info, (id, ctyp_args), args), ((_, l) as aux)) as instr -> (
          match extern_info with
          | Extern ret_ctyp ->
              if string_of_id id = "sail_cons" then (
                match args with
                | [hd_arg; tl_arg] ->
                    let ctyp_arg = C.ctyp_suprema (cval_ctyp hd_arg) in
                    if not (ctyp_equal (cval_ctyp hd_arg) ctyp_arg) then (
                      let gs = ngensym () in
                      let cast = [idecl l ctyp_arg gs; icopy l (CL_id (gs, ctyp_arg)) hd_arg] in
                      let cleanup = [iclear ~loc:l ctyp_arg gs] in
                      [
                        iblock
                          (cast
                          @ [
                              I_aux
                                (I_funcall (CR_one clexp, Extern ret_ctyp, (id, []), [V_id (gs, ctyp_arg); tl_arg]), aux);
                            ]
                          @ tail @ cleanup
                          );
                      ]
                    )
                    else instr :: tail
                | _ ->
                    (* cons must have two arguments *)
                    Reporting.unreachable (id_loc id) __POS__ "Invalid cons call"
              )
              else if
                (not (ctyp_equal (clexp_ctyp clexp) ret_ctyp))
                && not
                     (C.specialize_call_destination ctx id (List.map cval_ctyp args) ~semantic:ret_ctyp
                        ~represented:(clexp_ctyp clexp)
                     )
              then (
                let gs = ngensym () in
                let setup = [idecl l ret_ctyp gs] in
                let new_clexp = CL_id (gs, ret_ctyp) in
                let cleanup = [icopy l clexp (V_id (gs, ret_ctyp)); iclear ~loc:l ret_ctyp gs] in
                setup
                @ [I_aux (I_funcall (CR_one new_clexp, Extern ret_ctyp, (id, ctyp_args), args), aux)]
                @ cleanup @ tail
              )
              else instr :: tail
          | Call (((argument_intervals, result_interval), semantic_proofs) as callsite_info) -> (
              match get_function_typ id with
              | Some (param_ctyps, ret_ctyp) when C.make_call_precise ctx id param_ctyps ret_ctyp ->
                  if List.compare_lengths args param_ctyps <> 0 then
                    Reporting.unreachable (id_loc id) __POS__
                      ("Function call found with incorrect arity: " ^ string_of_id id);
                  (* Semantic call proofs can make a conversion exact even
                     when the independently inferred argument interval is
                     wider.  In particular, [right <= left] on subtraction
                     bounds a wide right operand by a native-width left
                     operand.  Refine the binary call intervals before
                     inserting argument casts so that exact casts retain an
                     explicit [Proven_narrow] marker. *)
                  let refine_argument_le left right intervals =
                    if Jib_semantics.has_argument_le ~left ~right semantic_proofs then (
                      match (List.nth_opt intervals left, List.nth_opt intervals right) with
                      | Some (Some (left_lower, left_upper)), Some (Some (right_lower, right_upper)) ->
                          List.mapi
                            (fun index interval ->
                              if index = left then Some (left_lower, Big_int.min left_upper right_upper)
                              else if index = right then Some (Big_int.max right_lower left_lower, right_upper)
                              else interval
                            )
                            intervals
                      | _ -> intervals
                    )
                    else intervals
                  in
                  let argument_intervals = argument_intervals |> refine_argument_le 0 1 |> refine_argument_le 1 0 in
                  let casted_args =
                    List.mapi
                      (fun index (arg, param_ctyp) ->
                        let arg_ctyp = cval_ctyp arg in
                        if
                          (not (ctyp_equal arg_ctyp param_ctyp))
                          && not
                               (C.specialize_call_argument ctx id (clexp_ctyp clexp) (List.map cval_ctyp args) index
                                  ~semantic:param_ctyp ~represented:arg_ctyp
                               )
                        then (
                          match
                            proven_fixed_integer_conversion param_ctyp
                              (Option.value ~default:None (List.nth_opt argument_intervals index))
                              arg
                          with
                          | Some converted ->
                              if !opt_debug_function_representations then
                                Printf.eprintf
                                  "C representation specialization: precise-call function=%s argument=%d source=%s \
                                   destination=%s proof=true\n\
                                   %!"
                                  (string_of_id id) index (string_of_ctyp arg_ctyp) (string_of_ctyp param_ctyp);
                              ([], converted, [])
                          | None ->
                              if !opt_debug_function_representations then
                                Printf.eprintf
                                  "C representation specialization: precise-call function=%s argument=%d source=%s \
                                   destination=%s proof=false\n\
                                   %!"
                                  (string_of_id id) index (string_of_ctyp arg_ctyp) (string_of_ctyp param_ctyp);
                              let gs = ngensym () in
                              let cast = [idecl l param_ctyp gs; icopy l (CL_id (gs, param_ctyp)) arg] in
                              let cleanup = [iclear ~loc:l param_ctyp gs] in
                              (cast, V_id (gs, param_ctyp), cleanup)
                        )
                        else ([], arg, [])
                      )
                      (List.combine args param_ctyps)
                  in
                  let ret_setup, clexp, ret_cleanup =
                    if
                      (not (ctyp_equal (clexp_ctyp clexp) ret_ctyp))
                      && not
                           (C.specialize_call_destination ctx id (List.map cval_ctyp args) ~semantic:ret_ctyp
                              ~represented:(clexp_ctyp clexp)
                           )
                    then (
                      let gs = ngensym () in
                      let result = V_id (gs, ret_ctyp) in
                      let result =
                        Option.value ~default:result
                          (proven_fixed_integer_conversion (clexp_ctyp clexp) result_interval result)
                      in
                      ([idecl l ret_ctyp gs], CL_id (gs, ret_ctyp), [icopy l clexp result; iclear ~loc:l ret_ctyp gs])
                    )
                    else ([], clexp, [])
                  in
                  let casts = List.map (fun (x, _, _) -> x) casted_args |> List.concat in
                  let args = List.map (fun (_, y, _) -> y) casted_args in
                  let cleanup = List.rev_map (fun (_, _, z) -> z) casted_args |> List.concat in
                  [
                    iblock1
                      (casts @ ret_setup
                      @ [I_aux (I_funcall (CR_one clexp, Call callsite_info, (id, ctyp_args), args), aux)]
                      @ tail @ ret_cleanup @ cleanup
                      );
                  ]
              | Some _ -> instr :: tail
              | None -> instr :: tail
            )
        )
      | instr -> instr :: tail
    in

    let rec precise_calls prior = function
      | (CDEF_aux (CDEF_type (CTD_variant (var_id, _, ctors)), _) as cdef) :: cdefs ->
          List.iter
            (fun (id, ctyp) -> constructor_types := Bindings.add id ([ctyp], CT_variant (var_id, [])) !constructor_types)
            ctors;
          precise_calls (cdef :: prior) cdefs
      | cdef :: cdefs -> precise_calls (cdef_map_funcall precise_call cdef :: prior) cdefs
      | [] -> List.rev prior
    in
    precise_calls [] cdefs

  (* Once we specialize variants, there may be additional type
     dependencies which could be in the wrong order. As such we need
     to sort the type definitions in the list of cdefs. *)
  let sort_ctype_defs ctx reverse cdefs =
    (* Split the cdefs into type definitions and non type definitions *)
    let is_ctype_def = function CDEF_aux (CDEF_type _, _) -> true | _ -> false in
    let unwrap = function CDEF_aux (CDEF_type ctdef, def_annot) -> (ctdef, def_annot) | _ -> assert false in
    let ctype_defs = List.map unwrap (List.filter is_ctype_def cdefs) in
    let cdefs = List.filter (fun cdef -> not (is_ctype_def cdef)) cdefs in

    let ctdef_id = function
      | CTD_abstract (id, _, _) | CTD_enum (id, _) | CTD_struct (id, _, _) | CTD_variant (id, _, _) | CTD_abbrev (id, _)
        ->
          id
    in

    let ctdef_ids = function
      | CTD_enum _ | CTD_abstract _ -> IdSet.empty
      | CTD_abbrev (_, ctyp) -> ctyp_ids ctyp
      | CTD_struct (_, _, ctors) | CTD_variant (_, _, ctors) ->
          List.fold_left (fun ids (_, ctyp) -> IdSet.union (ctyp_ids ctyp) ids) IdSet.empty ctors
    in

    let defined_type_ids =
      List.fold_left (fun ids (ctdef, _) -> IdSet.add (ctdef_id ctdef) ids) IdSet.empty ctype_defs
    in

    (* Create a reverse (i.e. from types to the types that are dependent
       upon them) id graph of dependencies between types *)
    let module IdGraph = Graph.Make (Id) in
    let graph =
      List.fold_left
        (fun g (ctdef, _) ->
          List.fold_left
            (fun g id -> IdGraph.add_edge id (ctdef_id ctdef) g)
            (IdGraph.add_edges (ctdef_id ctdef) [] g) (* Make sure even types with no dependencies are in graph *)
            (* Backends may use opaque JIB type identifiers whose concrete
               declarations are emitted by their code generator rather than
               represented by a CTD definition. *)
            (IdSet.elements (IdSet.inter defined_type_ids (ctdef_ids ctdef)))
        )
        IdGraph.empty ctype_defs
    in

    (* Then select the ctypes in the correct order as given by the topsort *)
    let ids = IdGraph.topsort graph in
    let ctype_defs =
      List.map
        (fun id ->
          let ctdef, def_annot = List.find (fun (ctdef, _) -> Id.compare (ctdef_id ctdef) id = 0) ctype_defs in
          CDEF_aux (CDEF_type ctdef, def_annot)
        )
        ids
    in

    (if reverse then List.rev ctype_defs else ctype_defs) @ cdefs

  let unit_tests_of_ast ast =
    List.fold_left
      (fun ids -> function
        | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, id, _), _)), def_annot)
          when Option.is_some (get_def_attribute "test" def_annot) ->
            IdSet.add id ids
        | _ -> ids
        )
      IdSet.empty ast.defs
    |> IdSet.elements

  let toplevel_lets_of_ast ast =
    let toplevel_lets_of_def = function DEF_aux (DEF_let (pat, _), _) -> pat_ids pat | _ -> IdSet.empty in
    let toplevel_lets_of_defs defs = List.fold_left IdSet.union IdSet.empty (List.map toplevel_lets_of_def defs) in
    toplevel_lets_of_defs ast.defs |> IdSet.elements

  class static_visitor statics =
    object
      inherit empty_jib_visitor

      method! vctyp _ = SkipChildren
      method! vclexp _ = SkipChildren
      method! vcval _ = SkipChildren

      method! vinstr =
        function
        | I_aux (I_init (ctyp, id, Init_static VL_undefined), (_, l)) ->
            statics := (l, ctyp, id, None) :: !statics;
            ChangeTo (Printf.ksprintf icomment "lifted %s" (string_of_name id))
        | I_aux (I_init (ctyp, id, Init_static vl), (_, l)) ->
            statics := (l, ctyp, id, Some vl) :: !statics;
            ChangeTo (Printf.ksprintf icomment "lifted %s" (string_of_name id))
        | _ -> DoChildren
    end

  let lift_statics cdefs =
    List.map
      (fun cdef ->
        let statics = ref [] in
        let cdef = visit_cdef (new static_visitor statics) cdef in
        List.rev_map
          (fun (l, ctyp, id, vl_opt) ->
            let annot = mk_def_annot l () |> add_def_attribute l "early_init" None in
            match vl_opt with
            | None -> CDEF_aux (CDEF_register (id, ctyp, []), annot)
            | Some vl -> CDEF_aux (CDEF_register (id, ctyp, [icopy l (CL_id (id, ctyp)) (V_lit (vl, ctyp))]), annot)
          )
          !statics
        @ [cdef]
      )
      cdefs
    |> List.concat

  let is_def_constraint = function DEF_aux (DEF_constraint _, _) -> true | _ -> false

  let first_env final_env = function [] -> final_env | DEF_aux (_, def_annot) :: _ -> def_annot.env

  (* This function helps optimise abstract types in the following way,
     if we see:

     {@sail[
       type x = ...
       constraint ...
       constraint ...
     ]}

     Then we move the typing environment from after the final
     constraint up to the [type], ensuring we pick the most optimised
     representation for that type declaration we safely can. *)
  let rec move_constraint_contexts final_env acc = function
    | DEF_aux (DEF_type tdef, def_annot) :: defs ->
        let constraints, rest = Util.take_drop is_def_constraint defs in
        let env = first_env final_env rest in
        move_constraint_contexts final_env
          (List.rev constraints @ [DEF_aux (DEF_type tdef, { def_annot with env })] @ acc)
          rest
    | def :: defs -> move_constraint_contexts final_env (def :: acc) defs
    | [] -> List.rev acc

  let compile_ast ctx ast =
    reset_representation_specializations ();
    let module G = Graph.Make (Callgraph.Node) in
    let g = Callgraph.graph_of_ast ast in
    let module NodeSet = Set.Make (Callgraph.Node) in
    (* Get the list of unit tests (valspecs with $[test]), so we can
       add them to the list of roots to avoid pruning them as
       dead-code. *)
    let unit_tests = unit_tests_of_ast ast in

    let roots =
      Specialize.get_initial_calls () @ unit_tests |> List.map (fun id -> Callgraph.Function id) |> NodeSet.of_list
    in
    let roots = IdSet.fold (fun id roots -> NodeSet.add (Callgraph.Type id) roots) C.preserve_types roots in
    let roots = NodeSet.add (Callgraph.Type (mk_id "exception")) roots in
    let roots =
      Bindings.fold (fun typ_id _ roots -> NodeSet.add (Callgraph.Type typ_id) roots) (Env.get_enums ctx.tc_env) roots
    in
    let roots =
      NodeSet.union (toplevel_lets_of_ast ast |> List.map (fun id -> Callgraph.Letbind id) |> NodeSet.of_list) roots
    in

    let g = G.prune roots NodeSet.empty g in
    let ast = Callgraph.filter_ast NodeSet.empty g ast in

    let total = List.length ast.defs in
    let _, chunks, ctx =
      List.fold_left
        (fun (n, chunks, ctx) def ->
          let defs, ctx = compile_def n total ctx def in
          (n + 1, defs :: chunks, ctx)
        )
        (1, [], ctx)
        (move_constraint_contexts ctx.tc_env [] ast.defs)
    in
    let chunks =
      Parmap.map ~parallelism:(Parmap.recommended_parallelism ())
        (function Compiled cdefs -> cdefs | Parallel f -> f ())
        chunks
    in
    let cdefs = List.concat (List.rev chunks) in

    (* If we don't have an exception type, add a dummy one *)
    let cdefs, ctx =
      if not (Bindings.mem (mk_id "exception") ctx.variants) then
        if C.assert_to_exception then (
          let assertion_failed = mk_id "__assertion_failed#" in
          ( CDEF_aux
              ( CDEF_type (CTD_variant (mk_id "exception", [], [(assertion_failed, CT_string)])),
                mk_def_annot Parse_ast.Unknown ()
              )
            :: cdefs,
            {
              ctx with
              variants =
                Bindings.add (mk_id "exception") ([], Bindings.singleton assertion_failed CT_string) ctx.variants;
            }
          )
        )
        else (
          let dummy_exn = mk_id "__dummy_exn#" in
          ( CDEF_aux
              ( CDEF_type (CTD_variant (mk_id "exception", [], [(dummy_exn, CT_unit)])),
                mk_def_annot Parse_ast.Unknown ()
              )
            :: cdefs,
            {
              ctx with
              variants = Bindings.add (mk_id "exception") ([], Bindings.singleton dummy_exn CT_unit) ctx.variants;
            }
          )
        )
      else (cdefs, ctx)
    in
    let cdefs, ctx = specialize_functions ctx cdefs in
    let cdefs, ctx = specialize_function_representations ctx cdefs in
    let cdefs = sort_ctype_defs ctx true cdefs in
    let cdefs, ctx = specialize_variants ctx [] cdefs in
    let cdefs = make_calls_precise ctx cdefs in
    let cdefs = sort_ctype_defs ctx false cdefs in
    let cdefs = lift_statics cdefs in
    if !opt_lint_readability then lint_jib_cdefs cdefs;
    (cdefs, ctx)
end
