import ExternObligations

open Sail.Specialization

def emptyExternDownstream : Semantics where
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
  jibEval := fun _ _ _ => True
  conversionEval := fun _ _ _ _ _ => True
  callArgumentsRepresent := fun _ _ _ => False
  sailCall := fun _ _ _ _ => True
  jibCall := fun _ _ _ _ _ => False
  externEval := fun _ _ _ => False
  sailReachable := fun _ _ => True
  boundsHold := fun _ _ => True
  outcomesRefine := fun _ _ => True
  exceptionsEquivalent := fun _ _ => True
  lifetimeCompatible := fun _ _ _ => True

theorem externRequiresExecution :
    ¬ obligation_4e81ef1ad207ac8ec4288e2a2826812a emptyExternDownstream := by
  intro obligation
  obtain ⟨_, _, callRepresentation, _, _⟩ := obligation [] () trivial
  exact callRepresentation

theorem externCallRequiresJibExecution :
    ¬ obligation_957a1e45102c495c424852247c6bd899 emptyExternDownstream := by
  intro obligation
  obtain ⟨_, _, callRepresentation, _, _⟩ := obligation [] () trivial
  exact callRepresentation

theorem completeRequiresExternCallRepresentation :
    ¬ Complete emptyExternDownstream := by
  intro complete
  obtain ⟨_, _, callRepresentation, _, _⟩ :=
    complete.proof_4e81ef1ad207ac8ec4288e2a2826812a [] () trivial
  exact callRepresentation
