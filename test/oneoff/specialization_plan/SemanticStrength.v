From Stdlib Require Import List.
Require Import SpecializationObligationsA.

Import ListNotations.
Import SailSpecialization.

Definition empty_downstream : Semantics :=
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

Theorem operation_requires_jib_execution :
  ~ obligation_493ba538f2348d395beed612b58cdbaf empty_downstream.
Proof.
  intro obligation.
  destruct (obligation [] [] tt I I) as [jib_outcome [jib_execution _]].
  exact jib_execution.
Qed.

Theorem call_requires_jib_execution :
  ~ obligation_508c5455ec087c4a8e55a60c0b16c5ed empty_downstream.
Proof.
  intro obligation.
  destruct (obligation [] [] tt I I) as [jib_outcome [jib_call _]].
  exact jib_call.
Qed.

Theorem conversion_requires_jib_execution :
  ~ obligation_faa8b1426e9792875f03d560ce6a2e15 empty_downstream.
Proof.
  intro obligation.
  destruct (obligation tt I) as [represented_value [conversion _]].
  exact conversion.
Qed.

Theorem exception_requires_jib_execution :
  ~ obligation_b3cb7325d6cf79449f3e7ed4c27cd4b2 empty_downstream.
Proof.
  intro obligation.
  destruct (obligation [] [] tt I I) as [jib_outcome [jib_execution _]].
  exact jib_execution.
Qed.

Theorem ownership_requires_jib_execution :
  ~ obligation_d23801564111e346f53bb752f78c6f81 empty_downstream.
Proof.
  intro obligation.
  destruct (obligation [] [] tt I I) as [jib_outcome [jib_execution _]].
  exact jib_execution.
Qed.

Theorem complete_requires_forward_execution : ~ Complete empty_downstream.
Proof.
  intro complete.
  exact (operation_requires_jib_execution
    (proof_493ba538f2348d395beed612b58cdbaf empty_downstream complete)).
Qed.

Definition source_unbounded : Semantics :=
  {| sem_value := unit;
     sem_outcome := unit;
     sem_arguments_well_typed := fun _ _ => True;
     sem_represented_values_valid := fun _ _ => True;
     sem_value_well_typed := fun _ _ => True;
     sem_represented_value_valid := fun _ _ => True;
     sem_value_satisfies_bound := fun _ _ => True;
     sem_arguments_represent := fun _ _ _ _ => False;
     sem_represents := fun _ _ _ _ => True;
     sem_sail_eval := fun _ _ _ => True;
     sem_jib_eval := fun _ _ _ => False;
     sem_conversion_eval := fun _ _ _ _ _ => False;
     sem_call_arguments_represent := fun _ _ _ => True;
     sem_sail_call := fun _ _ _ _ => True;
     sem_jib_call := fun _ _ _ _ _ => False;
     sem_extern_eval := fun _ _ _ => False;
     sem_sail_reachable := fun _ _ => True;
     sem_bounds_hold := fun _ _ => False;
     sem_outcomes_refine := fun _ _ => True;
     sem_exceptions_equivalent := fun _ _ => True;
     sem_lifetime_compatible := fun _ _ _ => True |}.

Theorem path_bounds_use_only_source_premises :
  ~ obligation_9c7bf89c7823fc4f0b1e85bcbf894021 source_unbounded.
Proof.
  intro obligation.
  exact (obligation [] I I).
Qed.
