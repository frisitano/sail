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
     sem_jib_eval := fun _ _ _ => False;
     sem_conversion_eval := fun _ _ _ _ _ => False;
     sem_call_arguments_represent := fun _ _ _ => True;
     sem_sail_call := fun _ _ _ _ => True;
     sem_jib_call := fun _ _ _ _ _ => False;
     sem_extern_eval := fun _ _ _ => False;
     sem_sail_reachable := fun _ _ => True;
     sem_bounds_hold := fun _ _ => True;
     sem_outcomes_refine := fun _ _ => True;
     sem_exceptions_equivalent := fun _ _ => True;
     sem_lifetime_compatible := fun _ _ _ => True |}.

Theorem extern_requires_execution :
  ~ obligation_4e81ef1ad207ac8ec4288e2a2826812a empty_extern_downstream.
Proof.
  intro obligation.
  destruct (obligation [] [] tt I I) as [extern_outcome [extern_execution _]].
  exact extern_execution.
Qed.

Theorem extern_call_requires_jib_execution :
  ~ obligation_957a1e45102c495c424852247c6bd899 empty_extern_downstream.
Proof.
  intro obligation.
  destruct (obligation [] [] tt I I) as [jib_outcome [jib_call _]].
  exact jib_call.
Qed.
