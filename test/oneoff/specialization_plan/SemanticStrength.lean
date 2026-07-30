import SpecializationObligationsA

open Sail.Specialization

def emptyDownstream : Semantics where
  Value := Unit
  Outcome := Unit
  argumentsWellTyped := fun _ _ => True
  representedValuesValid := fun _ _ => True
  valueWellTyped := fun _ _ => True
  representedValueValid := fun _ _ => True
  valueSatisfiesBound := fun _ _ => True
  argumentsRepresent := fun _ _ _ _ => True
  represents := fun _ _ _ _ => True
  sailEval := fun _ _ _ => True
  jibEval := fun _ _ _ => False
  conversionEval := fun _ _ _ _ _ => False
  callArgumentsRepresent := fun _ _ _ => True
  sailCall := fun _ _ _ _ => True
  jibCall := fun _ _ _ _ _ => False
  externEval := fun _ _ _ => False
  sailReachable := fun _ _ => True
  boundsHold := fun _ _ => True
  outcomesRefine := fun _ _ => True
  exceptionsEquivalent := fun _ _ => True
  lifetimeCompatible := fun _ _ _ => True

theorem operationRequiresJibExecution :
    ¬ obligation_493ba538f2348d395beed612b58cdbaf emptyDownstream := by
  intro obligation
  obtain ⟨_, jibExecution, _⟩ := obligation [] [] () trivial trivial
  exact jibExecution

theorem callRequiresJibExecution :
    ¬ obligation_508c5455ec087c4a8e55a60c0b16c5ed emptyDownstream := by
  intro obligation
  obtain ⟨_, jibCall, _⟩ := obligation [] [] () trivial trivial
  exact jibCall

theorem conversionRequiresJibExecution :
    ¬ obligation_faa8b1426e9792875f03d560ce6a2e15 emptyDownstream := by
  intro obligation
  obtain ⟨_, conversion, _⟩ := obligation () trivial
  exact conversion

theorem exceptionRequiresJibExecution :
    ¬ obligation_b3cb7325d6cf79449f3e7ed4c27cd4b2 emptyDownstream := by
  intro obligation
  obtain ⟨_, jibExecution, _⟩ := obligation [] [] () trivial trivial
  exact jibExecution

theorem ownershipRequiresJibExecution :
    ¬ obligation_d23801564111e346f53bb752f78c6f81 emptyDownstream := by
  intro obligation
  obtain ⟨_, jibExecution, _⟩ := obligation [] [] () trivial trivial
  exact jibExecution

theorem completeRequiresForwardExecution : ¬ Complete emptyDownstream := by
  intro complete
  exact operationRequiresJibExecution complete.proof_493ba538f2348d395beed612b58cdbaf

def sourceUnbounded : Semantics :=
  { emptyDownstream with
    argumentsRepresent := fun _ _ _ _ => False
    boundsHold := fun _ _ => False }

theorem pathBoundsUseOnlySourcePremises :
    ¬ obligation_9c7bf89c7823fc4f0b1e85bcbf894021 sourceUnbounded := by
  intro obligation
  exact obligation [] trivial trivial
