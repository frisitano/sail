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

(** Compile Sail ASTs to Jib intermediate representation *)

open Anf
open Ast
open Ast_compare
open Ast_defs
open Ast_util
open Jib
open Jib_util
open Type_check

(** This forces all integer struct fields to be represented as int64_t. Specifically intended for the various TLB
    structs in the ARM v8.5 spec. It is unsound in general. *)
val optimize_aarch64_fast_struct : bool ref

(** (WIP) [opt_memo_cache] will store the compiled function definitions in file _sbuild/ccacheDIGEST where DIGEST is the
    md5sum of the original function to be compiled. Enabled using the -memo flag. Uses Marshal so it's quite picky about
    the exact version of the Sail version. This cache can obviously become stale if the Sail changes - it'll load an old
    version compiled without said changes. *)
val opt_memo_cache : bool ref

(** Emit progress for fixed-integer representation inference and iterative function-clone worklist processing. The C
    backend exposes this as [--c-specialize-log]. *)
val opt_debug_function_representations : bool ref

(** Emit opt-in diagnostics for readability artifacts introduced by the common AST-to-Jib lowering. *)
val opt_lint_readability : bool ref

type jib_readability_finding = { rule : string; location : Parse_ast.l; message : string }

(** Analyze an instruction body without emitting diagnostics. This pure entry point keeps the post-Jib lint rules
    directly testable. *)
val jib_readability_findings : Jib.instr list -> jib_readability_finding list

(** Backend-neutral provenance captured when representation-specialized function clones are generated. Names are
    diagnostic only; consumers use the content-derived identities emitted by [Specialization_plan]. *)
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
      (** Source representation, destination representation, and whether the conversion carries compiler-reconstructed
          range evidence. *)
  conversions : (ctyp * ctyp * bool) list;
  recursive : bool;
}

val representation_specializations : representation_specialization list ref
val reset_representation_specializations : unit -> unit

(** Maximum number of distinct proof-backed C representation specializations generated for one source function.
    Exceeding the limit is an error rather than permission to route a caller through a weaker specialization. *)
val opt_max_function_specializations : int ref

(** {2 Jib context} *)

(* For an abstract type like `type xlen : Int`, is it initialised?
   Yes: `type xlen : Int = config xlen`
   No: `type xlen : Int`
*)
type abstract_type_initialised = Initialised | Uninitialised

type generic_signature = { generic_parameters : KidSet.t list; generic_result : KidSet.t }

(** Dynamic context for compiling Sail to Jib. We need to pass a (global) typechecking environment given by checking the
    full AST. *)
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

val ctx_is_extern : id -> ctx -> bool

val ctx_get_extern : id -> ctx -> string

val ctx_has_val_spec : id -> ctx -> bool

(** Create an inital Jib compilation context.

    The target is the name that would appear in a valspec extern section, i.e.

    {v val foo = { systemverilog: "bar", c: "baz" } = ... v}

    would mean "systemverilog" and "c" would be valid for_target parameters. If unspecified it will get the current
    target name from the Target module. If unspecified and there is no current target, it defaults to "c". *)
val initial_ctx : ?for_target:string -> Env.t -> Effects.side_effect_info -> ctx

type funwire = Arg of int | Ret | Invoke

val transparent_newtype : ctx -> ctyp -> ctyp

val struct_field_bindings : Ast.l -> ctx -> ctyp -> Ast.id * ctyp Bindings.t

val struct_fields : Ast.l -> ctx -> ctyp -> Ast.id * (Ast.id -> ctyp)

val variant_constructor_bindings : Ast.l -> ctx -> ctyp -> Ast.id * ctyp Bindings.t

val enum_members : Ast.l -> ctx -> Ast.id -> IdSet.t

(** {2 Compilation functions} *)

(** The Config module specifies static configuration for compiling Sail into Jib. We have to provide a conversion
    function from Sail types into Jib types, as well as a function that optimizes ANF expressions (which can just be the
    identity function) *)
module type CONFIG = sig
  val convert_typ : ctx -> typ -> ctyp

  (** Choose the representation used when a concrete type becomes a generic container argument. *)
  val ctyp_suprema : ctyp -> ctyp

  (** Optionally replace the compiled payload of a nominal newtype. *)
  val specialize_newtype_payload : id -> ctyp -> ctyp

  (** Optionally replace the backend representation of a record field. This changes only the JIB/backend carrier; the
      source-language field keeps its original semantic type. *)
  val specialize_struct_field : id -> id -> ctyp -> ctyp

  (** Optionally select backend representations for source-declared function arguments and results. The source type has
      already passed Sail's type checker; this hook changes only the JIB/backend carrier. *)
  val specialize_declared_function_argument : id -> int -> ctyp -> ctyp

  val specialize_declared_function_result : id -> ctyp -> ctyp

  (** Whether an ANF temporary whose semantic type is [semantic] may retain [represented] even when the temporary is
      marked mutable by ANF construction. This is intentionally narrower than [representation_refines]: most mutable
      source values require whole-lifetime analysis, while representation-preserving address arithmetic must not
      immediately convert a pointer back to an integer. *)
  val propagate_anf_temporary_representation : semantic:ctyp -> represented:ctyp -> bool

  (** Return true when [represented] is a backend-specific, lossless representation of [semantic]. This keeps such
      values in their native representation while compiling newtype destructuring and local bindings, until a real
      semantic-type boundary requires conversion. *)
  val representation_refines : semantic:ctyp -> represented:ctyp -> bool

  (** Return true when a local Sail function should be cloned with [represented] in place of a [semantic] parameter.
      Calls to the clone keep the narrower representation instead of inserting a conversion at the ordinary function
      boundary. The clone is generated on demand from the original JIB body; external functions are never specialized
      this way. *)
  val specialize_function_argument_representation : semantic:ctyp -> represented:ctyp -> bool

  (** Return true when a local Sail function should be cloned with [represented] in place of its [semantic] result. This
      is the result counterpart of [specialize_function_argument_representation]. *)
  val specialize_function_result_representation : semantic:ctyp -> represented:ctyp -> bool

  (** Return true when a specialized parameter or result representation must be propagated through the cloned function
      body. Numeric subtype specialization normally changes only the named parameter storage; structural representations
      such as native wide bits and fixed byte vectors must replace the corresponding generic JIB type throughout the
      clone. *)
  val specialize_function_body_representation : semantic:ctyp -> represented:ctyp -> bool

  (** Permit immutable top-level [int] bindings to use the exact finite lifetime inferred from their initializer.
      Specializing backends use this for expressions such as [unsigned(0x...)]; ordinary backends retain the semantic
      mathematical-integer representation. *)
  val specialize_c : bool

  (** Reject arbitrary-precision integers that remain after specialization. This is an audit only and must not affect
      representation selection. *)
  val require_bounded_int : bool

  val integer_representation_bounds : ctyp -> (Big_int.num * Big_int.num) option

  (** Optionally replace a representation-specialized local function clone by a backend primitive. The source function
      and its ordinary ABI remain canonical; this hook is considered only after a concrete represented parameter/result
      signature has demanded a clone. *)
  val specialized_function_external : id -> ctyp list -> ctyp -> id option

  (** Return the compatibility view used while unifying a function argument. This allows a semantic fixed vector and its
      backend representation to meet at a call boundary before [make_calls_precise] inserts any required adapter. The
      argument itself retains [represented]. *)
  val function_argument_unification_type : expected:ctyp -> represented:ctyp -> ctyp option

  (** Return true when an argument whose typed source expression is [source] may cross an [expected] function boundary
      through the backend's narrowing conversion machinery. This is separate from representation specialization:
      [source] supplies the semantic proof that a larger storage representation fits [expected], whereas a narrower
      native representation must select a cloned local function and remain narrow. *)
  val function_argument_narrowing_allowed : expected:ctyp -> source:ctyp -> represented:ctyp -> bool

  (** Return true when an ANF value carrying [semantic] may remain in [represented] without crossing a checked
      conversion boundary. *)
  val preserve_aval_representation : semantic:ctyp -> represented:ctyp -> bool

  (** Return true when a newtype constructor may demand [represented] directly from its payload expression. This is
      deliberately stricter than [representation_refines]: checked numeric newtypes must first evaluate their
      mathematical Sail value and only then cross the checked packing boundary. *)
  val propagate_newtype_payload_representation : id -> semantic:ctyp -> represented:ctyp -> bool

  (** Preserve a backend-specific result representation across an external operation when its represented arguments
      determine the result layout. [id] is the external implementation name, not necessarily the Sail source identifier.
  *)
  val specialize_call_result : id -> ctyp list -> ctyp -> ctyp

  (** Return true only when the implementation of [id] can write its semantic result directly into [represented]. This
      is intentionally narrower than [representation_refines], because ordinary runtime functions still use their
      declared Sail/GMP calling convention. *)
  val specialize_call_destination : ctx -> id -> ctyp list -> semantic:ctyp -> represented:ctyp -> bool

  (** Keep an argument in a backend-specific representation when a specialized result or another represented argument
      supplies the matching native implementation. The list contains every argument's representation before
      call-boundary conversions. *)
  val specialize_call_argument : ctx -> id -> ctyp -> ctyp list -> int -> semantic:ctyp -> represented:ctyp -> bool

  val optimize_anf : ctx -> typ aexp -> typ aexp

  (** Unroll all for loops a bounded number of times. Used for SMT generation. *)
  val unroll_loops : int option

  (** A call is precise if the function arguments match the function type exactly. Leaving functions imprecise can allow
      later passes to specialize implementations. *)
  val make_call_precise : ctx -> id -> ctyp list -> ctyp -> bool

  (** If false, will ensure that fixed size bitvectors are specifically less that 64-bits. If true this restriction will
      be ignored. *)
  val ignore_64 : bool

  (** If false we won't generate any V_struct values *)
  val struct_value : bool

  (** If false we won't generate any V_tuple values *)
  val tuple_value : bool

  (** Allow real literals *)
  val use_real : bool

  (** Insert branch coverage operations *)
  val branch_coverage : out_channel option

  (** If true track the location of the last exception thrown, useful for debugging C but we want to turn it off for SMT
      generation where we can't use strings *)
  val track_throw : bool

  (** Assertions in the Sail code will be compiled to exceptions in the Jib output *)
  val assert_to_exception : bool

  (** Compile assertion conditions without carrying their diagnostic Sail strings into Jib. Used by fixed-representation
      backends that lower a failed assertion directly to a target trap. *)
  val erase_assert_messages : bool

  val use_void : bool

  (** Convert control flow where all branches are pure into, into eager variants, i.e.

      let x = if b else y then z

      becomes

      let x = eager_if(b, y, z)

      so `y` and `z` are eagerly evaluated before the if-statement which just becomes like a function call. Reducing the
      control-flow like this is useful for the Sail->SV and Sail->SMT backends. *)
  val eager_control_flow : bool

  (** Types to preserve in the Jib output *)
  val preserve_types : IdSet.t

  val fun_to_wires : int Bindings.t
end

module IdGraph : sig
  include Graph.S with type node = id and type node_set = IdSet.t
end

val callgraph : cdef list -> IdGraph.graph

module Make (C : CONFIG) : sig
  val compile_ast : ctx -> typed_ast -> cdef list * ctx
end
