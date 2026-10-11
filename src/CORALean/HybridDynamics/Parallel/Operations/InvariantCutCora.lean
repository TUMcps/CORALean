
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
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's condition as MATLAB parses it: `polytope || (levelSet && labelMerged)`. -/
def ParallelHybridAutomaton.invariantCutCora (isPolytope isLevelSet labelMerged : Bool) : Bool :=
  isPolytope || (isLevelSet && labelMerged)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
