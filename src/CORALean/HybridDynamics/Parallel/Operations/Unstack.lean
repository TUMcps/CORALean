import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

/-!
# `unstack`

The inverse of `stack`: block `i` of a point of the product space. `Theorems.StackUnstack` and
`Theorems.UnstackStack` say the two undo each other.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def unstack (z : Vec ℝ (∑ i, n i)) : ∀ i, Vec ℝ (n i) :=
  fun i j => z (finSigmaFinEquiv ⟨i, j⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
