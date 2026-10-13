module

@[expose] public section

/-!
# The invariant cut as `mergeInvariants.m` documents it

A polytope or level-set guard whose synchronization label is merged: the condition the comment
in CORA's `@parallelHybridAutomaton/mergeInvariants.m` states, against which `invariantCutCora`
is what the code computes (#40).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The condition as its comment documents it: a polytope or level-set guard whose label is
merged. -/
def ParallelHybridAutomaton.invariantCutDocumented (isPolytope isLevelSet labelMerged : Bool) :
    Bool :=
  (isPolytope || isLevelSet) && labelMerged

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
