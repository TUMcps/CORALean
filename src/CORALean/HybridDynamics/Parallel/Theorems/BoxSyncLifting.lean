module

public import CORALean.HybridDynamics.Parallel.Theorems.BoxLifting
public import CORALean.HybridDynamics.Parallel.Definitions.SyncLifting
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# `boxSyncLifting`: `boxLifting` with conjoined guards

`boxLifting` and `SyncLifting.guardAll` as `HPolytope.stackProd` of the participants' guards, a
component with no guard contributing the whole space. The stack of a tuple of points is in it
exactly when every present guard holds at its block.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {k m : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.boxSyncLifting (binds : ∀ i, Fin (n i) → InputSource k n m) :
    ParallelHybridAutomaton.SyncLifting (ℐ𝒱)
      (ℋ𝒫) n m binds where
  toLifting := ParallelHybridAutomaton.boxLifting binds
  guardAll gs := HPolytope.stackProd fun i => match gs i with
    | some g => g
    | none => HPolytope.fullspace (Vec ℝ (n i))
  mem_guardAll gs x hx := by
    show stack x ∈ (HPolytope.stackProd _).construct
    rw [HPolytope.stackProd_exact]
    intro i
    rw [unstack_stack]
    cases hg : gs i with
    | some g => exact hx i g hg
    | none => simp [HPolytope.construct_fullspace]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
