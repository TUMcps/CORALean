module

public import CORALean.HybridDynamics.Parallel.Operations.InvariantCutDocumented

@[expose] public section

/-!
# When CORA cuts an invariant by a guard's complement

CORA's `@parallelHybridAutomaton/mergeInvariants.m` intersects a component's invariant with the
complement of a transition's guard on the condition

    isa(guard,'polytope') || isa(guard,'levelSet') && ismember(syncLabel, mergedLabels)

whose comment says "if the corresponding transition's synchronization label is active in the
composed location". MATLAB's `&&` binds tighter than `||`, so the condition is
`isPolytope || (isLevelSet && labelMerged)`, which is `invariantCutCora`: a polytope guard is
cut whether or not its label is merged, an unlabeled transition's included. The documented reading
is `invariantCutDocumented`. The two differ (`Theorems.InvariantCutCoraCounterexample`).

Neither is made by `mergeInvariants` here, which does not cut (#40).

# CORA's invariant cut is not the one it documents

A polytope guard whose label is not merged (an unlabeled transition's included): CORA cuts the
invariant by its complement, the documented condition does not. Read from
`@parallelHybridAutomaton/mergeInvariants.m`, not run (#40,
`references/coverage/hybridDynamics/parallelHybridAutomaton.md`, row `mergeInvariants`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA cuts the invariant, the documented condition does not
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's condition as MATLAB parses it: `polytope || (levelSet && labelMerged)`. -/
def ParallelHybridAutomaton.invariantCutCora (isPolytope isLevelSet labelMerged : Bool) : Bool :=
  isPolytope || (isLevelSet && labelMerged)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.invariantCutCora_counterexample :
    ParallelHybridAutomaton.invariantCutCora true false false = true ∧
      ParallelHybridAutomaton.invariantCutDocumented true false false = false := by
  exact ⟨rfl, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
