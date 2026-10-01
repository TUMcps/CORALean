import CORALean.HybridDynamics.Parallel.Operations.Unstack

/-!
# `unstack` undoes `stack`

The blocks of a stack are what was stacked. `Theorems.StackUnstack` is the other way round.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem unstack_stack (x : ∀ i, Vec ℝ (n i)) : unstack (stack x) = x := by
  funext i j
  unfold unstack stack
  rw [Equiv.symm_apply_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
