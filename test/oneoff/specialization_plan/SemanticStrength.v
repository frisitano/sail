From Stdlib Require Import List String.
Require Import SpecializationObligationsA.

Import ListNotations.
Import SailSpecialization.
Open Scope string_scope.

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
     sem_call_arguments_represent := fun _ _ _ => False;
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

Theorem call_requires_representation_and_jib_execution :
  ~ obligation_508c5455ec087c4a8e55a60c0b16c5ed empty_downstream.
Proof.
  intro obligation.
  destruct (obligation [] tt I)
    as [represented_args [jib_outcome [call_representation _]]].
  exact call_representation.
Qed.

Theorem conversion_requires_jib_execution :
  ~ obligation_faa8b1426e9792875f03d560ce6a2e15 empty_downstream.
Proof.
  intro obligation.
  destruct (obligation tt I) as [represented_value [conversion _]].
  exact conversion.
Qed.

Theorem complete_requires_forward_execution : ~ Complete empty_downstream.
Proof.
  intro complete.
  exact (operation_requires_jib_execution
    (proof_493ba538f2348d395beed612b58cdbaf empty_downstream complete)).
Qed.

Definition missing_call_representation : Semantics :=
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
     sem_conversion_eval := fun _ _ _ _ _ => True;
     sem_call_arguments_represent := fun _ _ _ => False;
     sem_sail_call := fun _ _ _ _ => True;
     sem_jib_call := fun _ _ _ _ _ => False;
     sem_extern_eval := fun _ _ _ => False;
     sem_sail_reachable := fun _ _ => True;
     sem_bounds_hold := fun _ _ => True;
     sem_outcomes_refine := fun _ _ => True;
     sem_exceptions_equivalent := fun _ _ => True;
     sem_lifetime_compatible := fun _ _ _ => True |}.

Theorem complete_requires_call_representation :
  ~ Complete missing_call_representation.
Proof.
  intro complete.
  destruct
    (proof_508c5455ec087c4a8e55a60c0b16c5ed
      missing_call_representation complete [] tt I)
    as [represented_args [jib_outcome [call_representation _]]].
  exact call_representation.
Qed.

Definition split_outcome_conditions : Semantics :=
  {| sem_value := unit;
     sem_outcome := bool;
     sem_arguments_well_typed := fun _ _ => True;
     sem_represented_values_valid := fun _ _ => True;
     sem_value_well_typed := fun _ _ => True;
     sem_represented_value_valid := fun _ _ => True;
     sem_value_satisfies_bound := fun _ _ => True;
     sem_arguments_represent := fun _ _ _ _ => True;
     sem_represents := fun _ _ _ _ => True;
     sem_sail_eval := fun _ _ outcome => outcome = false;
     sem_jib_eval := fun _ _ _ => True;
     sem_conversion_eval := fun _ _ _ _ _ => True;
     sem_call_arguments_represent := fun _ _ _ => True;
     sem_sail_call := fun _ _ _ _ => True;
     sem_jib_call := fun _ _ _ _ _ => True;
     sem_extern_eval := fun _ _ _ => True;
     sem_sail_reachable := fun _ _ => True;
     sem_bounds_hold := fun _ _ => True;
     sem_outcomes_refine := fun _ _ => True;
     sem_exceptions_equivalent := fun _ jib_outcome => jib_outcome = false;
     sem_lifetime_compatible := fun _ _ jib_outcome => jib_outcome = true |}.

Theorem exception_safety_rejects_split_outcome :
  ~ obligation_b3cb7325d6cf79449f3e7ed4c27cd4b2 split_outcome_conditions.
Proof.
  intro obligation.
  specialize (obligation [] [] false true I eq_refl I I).
  discriminate.
Qed.

Theorem ownership_safety_rejects_split_outcome :
  ~ obligation_d23801564111e346f53bb752f78c6f81 split_outcome_conditions.
Proof.
  intro obligation.
  specialize (obligation [] [] false false I eq_refl I I).
  discriminate.
Qed.

Theorem complete_rejects_split_outcome_conditions :
  ~ Complete split_outcome_conditions.
Proof.
  intro complete.
  exact (exception_safety_rejects_split_outcome
    (proof_b3cb7325d6cf79449f3e7ed4c27cd4b2 split_outcome_conditions complete)).
Qed.

Theorem no_execution_has_both_side_conditions :
  ~ exists jib_outcome,
      sem_jib_eval split_outcome_conditions "clone" [] jib_outcome /\
      sem_outcomes_refine split_outcome_conditions false jib_outcome /\
      sem_exceptions_equivalent split_outcome_conditions false jib_outcome /\
      sem_lifetime_compatible split_outcome_conditions "clone" [] jib_outcome.
Proof.
  intros [jib_outcome [_ [_ [exception_equivalence lifetime_compatibility]]]].
  destruct jib_outcome; discriminate.
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
