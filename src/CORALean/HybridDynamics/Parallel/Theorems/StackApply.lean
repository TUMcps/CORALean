import CORALean.HybridDynamics.Parallel.Operations.Unstack

/-!
# A coordinate of a stack

Coordinate `⟨i, j⟩` of the stack is coordinate `j` of block `i`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem stack_apply (x : ∀ i, Vec ℝ (n i)) (i : Fin k) (j : Fin (n i)) :
    stack x (finSigmaFinEquiv ⟨i, j⟩) = x i j := by
  unfold stack
  rw [Equiv.symm_apply_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
