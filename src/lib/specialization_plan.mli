(****************************************************************************)
(* Backend-neutral representation-specialization provenance.               *)
(****************************************************************************)

type t

val create :
  compiler_name:string ->
  compiler_version:string ->
  compiler_revision:string option ->
  configuration:string ->
  input_locations:Ast.l list ->
  Jib_compile.representation_specialization list ->
  t

val write_json : string -> t -> unit

val write_lean : string -> t -> unit
val write_coq : string -> t -> unit

(** The backend-symbol callback is used only for the non-authoritative human report. Backend symbols are deliberately
    absent from the machine plan and all proof identities. *)
val write_human : backend_symbol:(Ast.id -> string) -> string -> t -> unit
