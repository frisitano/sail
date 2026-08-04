From Stdlib Require Import List.
Require Import ExternObligations.

Import ListNotations.
Import SailSpecialization.

Definition empty_extern_downstream : Semantics :=
  {| sem_value := unit;
     sem_outcome := unit;
     sem_arguments_well_typed := fun _ _ => True;
     sem_represented_values_valid := fun _ _ => True;
     sem_value_well_typed := fun _ _ => True;
     sem_represented_value_valid := fun _ _ => True;
     sem_value_satisfies_bound := fun _ _ => True;
     sem_arguments_represent := fun _ _ _ _ => True;
     sem_represents := fun _ _ _ _ => True;
     sem_sail_eval := fun _ _ _ => True;
     sem_jib_eval := fun _ _ _ => True;
     sem_conversion_eval := fun _ _ _ _ _ _ => True;
     sem_call_arguments_represent := fun _ _ _ => False;
     sem_sail_call := fun _ _ _ _ => True;
     sem_jib_call := fun _ _ _ _ _ => False;
     sem_extern_eval := fun _ _ _ => False;
     sem_sail_reachable := fun _ _ => True;
     sem_bounds_hold := fun _ _ => True;
     sem_outcomes_refine := fun _ _ => True;
     sem_exceptions_equivalent := fun _ _ => True;
     sem_lifetime_compatible := fun _ _ _ => True |}.

Theorem extern_requires_execution :
  ~ obligation_cfa887618ae50fd81658d418638415d6 empty_extern_downstream.
Proof.
  intro obligation.
  destruct (obligation [] tt I)
    as [represented_args [extern_outcome [call_representation _]]].
  exact call_representation.
Qed.

Theorem extern_call_requires_jib_execution :
  ~ obligation_7f90599935e30f34f3effd3005354d2e empty_extern_downstream.
Proof.
  intro obligation.
  destruct (obligation [] tt I)
    as [represented_args [jib_outcome [call_representation _]]].
  exact call_representation.
Qed.

Theorem complete_requires_extern_call_representation :
  ~ Complete empty_extern_downstream.
Proof.
  intro complete.
  destruct
    (proof_cfa887618ae50fd81658d418638415d6
      empty_extern_downstream complete [] tt I)
    as [represented_args [extern_outcome [call_representation _]]].
  exact call_representation.
Qed.

Definition extern_observation
    (extern_execution outcomes_refine : Prop) : Semantics :=
  {| sem_value := unit;
     sem_outcome := unit;
     sem_arguments_well_typed := fun _ _ => True;
     sem_represented_values_valid := fun _ _ => True;
     sem_value_well_typed := fun _ _ => True;
     sem_represented_value_valid := fun _ _ => True;
     sem_value_satisfies_bound := fun _ _ => True;
     sem_arguments_represent := fun _ _ _ _ => True;
     sem_represents := fun _ _ _ _ => True;
     sem_sail_eval := fun _ _ _ => True;
     sem_jib_eval := fun _ _ _ => True;
     sem_conversion_eval := fun _ _ _ _ _ _ => True;
     sem_call_arguments_represent := fun _ _ _ => True;
     sem_sail_call := fun _ _ _ _ => True;
     sem_jib_call := fun _ _ _ _ _ => True;
     sem_extern_eval := fun _ _ _ => extern_execution;
     sem_sail_reachable := fun _ _ => True;
     sem_bounds_hold := fun _ _ => True;
     sem_outcomes_refine := fun _ _ => outcomes_refine;
     sem_exceptions_equivalent := fun _ _ => True;
     sem_lifetime_compatible := fun _ _ _ => True |}.

Definition missing_extern_execution : Semantics :=
  extern_observation False True.

Theorem extern_requires_extern_execution :
  ~ obligation_cfa887618ae50fd81658d418638415d6 missing_extern_execution.
Proof.
  intro obligation.
  destruct (obligation [] tt I)
    as [represented_args [extern_outcome [_ [extern_execution _]]]].
  exact extern_execution.
Qed.

Definition missing_extern_outcome_refinement : Semantics :=
  extern_observation True False.

Theorem extern_requires_outcome_refinement :
  ~ obligation_cfa887618ae50fd81658d418638415d6
      missing_extern_outcome_refinement.
Proof.
  intro obligation.
  destruct (obligation [] tt I)
    as [represented_args [extern_outcome [_ [_ refinement]]]].
  exact refinement.
Qed.
