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
    ¬ obligation_cfa887618ae50fd81658d418638415d6 emptyExternDownstream := by
  intro obligation
  obtain ⟨_, _, callRepresentation, _, _⟩ := obligation [] () trivial
  exact callRepresentation

theorem externCallRequiresJibExecution :
    ¬ obligation_7f90599935e30f34f3effd3005354d2e emptyExternDownstream := by
  intro obligation
  obtain ⟨_, _, callRepresentation, _, _⟩ := obligation [] () trivial
  exact callRepresentation

theorem completeRequiresExternCallRepresentation :
    ¬ Complete emptyExternDownstream := by
  intro complete
  obtain ⟨_, _, callRepresentation, _, _⟩ :=
    complete.proof_cfa887618ae50fd81658d418638415d6 [] () trivial
  exact callRepresentation

def missingExternExecution : Semantics :=
  { emptyExternDownstream with
    callArgumentsRepresent := fun _ _ _ => True }

theorem externRequiresExternExecution :
    ¬ obligation_cfa887618ae50fd81658d418638415d6 missingExternExecution := by
  intro obligation
  obtain ⟨_, _, _, externExecution, _⟩ := obligation [] () trivial
  exact externExecution

def missingExternOutcomeRefinement : Semantics :=
  { missingExternExecution with
    externEval := fun _ _ _ => True
    outcomesRefine := fun _ _ => False }

theorem externRequiresOutcomeRefinement :
    ¬ obligation_cfa887618ae50fd81658d418638415d6 missingExternOutcomeRefinement := by
  intro obligation
  obtain ⟨_, _, _, _, refinement⟩ := obligation [] () trivial
  exact refinement
