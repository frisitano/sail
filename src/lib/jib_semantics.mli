open Ast
open Jib
open Type_check

module InstructionSet : Set.S with type elt = int

type operation = Add | Subtract | Multiply

type reduction = Truncating | Euclidean

type observation = Exact | Low_bits of int | Checked | Saturating

type comparison = Equal | Not_equal | Less_than | Less_equal | Greater_than | Greater_equal

type identity = { owner : id; instruction : int }

type fact = { logical_type : ctyp; interval : integer_interval option; unsigned : bool }

type evidence = {
  identity : identity;
  operation : operation;
  reduction : reduction;
  observation : observation;
  modulus : Nat_big_num.num;
  operands : fact list;
  proofs : semantic_proof list;
  dependencies : InstructionSet.t;
}

type t

val empty : t
val record : evidence -> t -> t
val find : instruction:int -> t -> evidence option
val invalidate_missing : InstructionSet.t -> t -> t
val bindings : t -> evidence list

(** Inclusive bounds for an unsigned value represented by exactly [width] bits. *)
val fixed_unsigned_bounds : int -> integer_interval option

(** Structurally prove that [mask] is exactly the low [n] one-bits of a
    [carrier_width]-bit unsigned word, returning [n]. Zero, negative,
    non-contiguous, and over-wide masks are rejected. *)
val prove_low_mask_width : carrier_width:int -> mask:Nat_big_num.num -> int option

(** Refine the inclusive bounds of both operands on one edge of an integer
    comparison. [None] means the edge is infeasible. This is a semantic range
    operation and deliberately does not select a target representation. *)
val refine_comparison_bounds :
  comparison ->
  truth:bool ->
  left:integer_interval ->
  right:integer_interval ->
  (integer_interval * integer_interval) option

(** Derive composable unsigned result bounds from fixed-width bit operations. These rules are deliberately
    independent of any C representation: later graph and lowering passes may consume the same facts. *)
val slice_result_bounds :
  width:int -> source:integer_interval option -> start:integer_interval option -> integer_interval option

val concat_result_bounds :
  right_width:int -> left:integer_interval option -> right:integer_interval option -> integer_interval option

val bitwise_and_result_bounds :
  left:integer_interval option -> right:integer_interval option -> integer_interval option

val bitwise_union_result_bounds :
  left:integer_interval option -> right:integer_interval option -> integer_interval option

val bit_insert_result_bounds :
  carrier_width:int ->
  base:integer_interval option ->
  start:integer_interval option ->
  inserted:integer_interval option ->
  integer_interval option

(** Prove that every value denoted by one call argument is no greater than every value denoted by another. Concrete
    intervals are checked first; symbolic ranges fall back to Sail's cached type-constraint prover. *)
val prove_argument_le :
  env:Env.t ->
  left_index:int ->
  left_typ:typ ->
  left_interval:integer_interval option ->
  right_index:int ->
  right_typ:typ ->
  right_interval:integer_interval option ->
  semantic_proof option

(** Prove that every value denoted by a call result is nonnegative. This is deliberately operation-neutral: consumers
    decide which transformations can soundly use the fact. *)
val prove_result_nonnegative :
  env:Env.t -> result_typ:typ -> result_interval:integer_interval option -> semantic_proof option

(** Prove inclusive lower and upper bounds for every value denoted by a call argument. *)
val prove_argument_bounds :
  env:Env.t ->
  index:int ->
  typ:typ ->
  interval:integer_interval option ->
  lower:Nat_big_num.num ->
  upper:Nat_big_num.num ->
  semantic_proof option

(** Prove inclusive lower and upper bounds for every value denoted by a call result. *)
val prove_result_bounds :
  env:Env.t ->
  result_typ:typ ->
  result_interval:integer_interval option ->
  lower:Nat_big_num.num ->
  upper:Nat_big_num.num ->
  semantic_proof option

(** Prove structurally that zero-extension from one fixed bitvector width to another preserves the source value. *)
val prove_conversion_value_preserving : source_width:int -> target_width:int -> semantic_proof option

(** Prove structurally that sign-extension preserves the signed value represented by a fixed bitvector. *)
val prove_signed_conversion_value_preserving : source_width:int -> target_width:int -> semantic_proof option

(** Prove structurally that truncation observes exactly the requested low bits of a fixed bitvector. *)
val prove_conversion_low_bits : source_width:int -> target_width:int -> semantic_proof option

(** Prove that a shift count is within the range defined by a selected native C carrier. Concrete intervals are
    preferred; symbolic Sail constraints use the same cached prover as the other semantic obligations. *)
val prove_shift_count_bounds :
  env:Env.t -> index:int -> typ:typ -> interval:integer_interval option -> carrier_width:int -> semantic_proof option

(** Prove a defined native shift directly from an inferred interval. This is
    used after path analysis, when the source Sail type is no longer attached
    to the JIB value but the branch-refined semantic interval is available. *)
val prove_shift_count_interval :
  index:int -> interval:integer_interval option -> carrier_width:int -> semantic_proof option

(** Prove that a fixed-width bit insertion position keeps the entire inserted
    value within its carrier. The resulting argument-bounds certificate lets
    a backend select an unchecked native mask/shift implementation. *)
val prove_bit_insert_position_bounds :
  env:Env.t ->
  index:int ->
  typ:typ ->
  interval:integer_interval option ->
  carrier_width:int ->
  inserted_width:int ->
  semantic_proof option

val has_argument_le : left:int -> right:int -> semantic_proof list -> bool
val has_argument_bounds : index:int -> lower:Nat_big_num.num -> upper:Nat_big_num.num -> semantic_proof list -> bool
val has_result_bounds : lower:Nat_big_num.num -> upper:Nat_big_num.num -> semantic_proof list -> bool
val has_result_nonnegative : semantic_proof list -> bool
val has_conversion_value_preserving : source_width:int -> target_width:int -> semantic_proof list -> bool
val has_signed_conversion_value_preserving : source_width:int -> target_width:int -> semantic_proof list -> bool
val has_conversion_low_bits : source_width:int -> target_width:int -> semantic_proof list -> bool
val has_shift_count_bounds : index:int -> carrier_width:int -> semantic_proof list -> bool
