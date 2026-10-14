module

public import CORALean.HybridDynamics.Parallel.Operations.Basic

@[expose] public section

/-!
# `stack` undoes `unstack`

The stack of the blocks of a point is the point: every point of the product space is a stack,
which is what lets a statement about the product be read off its components.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem stack_unstack (z : Vec ℝ (∑ i, n i)) : stack (unstack z) = z := by
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  unfold unstack stack
  rw [Equiv.symm_apply_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
