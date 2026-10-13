import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

/-!
# `unstack`

The inverse of `stack`: block `i` of a point of the product space. `Theorems.StackUnstack` and
`Theorems.UnstackStack` say the two undo each other.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def unstack (z : Vec ℝ (∑ i, n i)) : ∀ i, Vec ℝ (n i) :=
  fun i j => z (finSigmaFinEquiv ⟨i, j⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
