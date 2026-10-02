import CORALean.ContSet.Interval.Real.Operations.Diag

/-!
# `Interval.diag` is exactly the set of diagonal matrices over the box

The diagonal matrices over a vector box are exactly the box `diag` builds: its off-diagonal
entries are the point `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.diag_exact (I : Interval (Vec ℝ n)) :
    I.diag.construct = Matrix.diagonal '' I.construct := by -- --- PROOF ---
  ext B
  constructor
  -- a diagonal-box matrix has zero off the diagonal, and its diagonal lies in the vector box
  · intro hB
    have hoff : ∀ i j, i ≠ j → B i j = 0 := fun i j hij => by
      have h := hB (i, j)
      simp only [Interval.diag, Entrywise.entry_mat, Matrix.diagonal_apply_ne _ hij] at h
      exact le_antisymm h.2 h.1
    refine ⟨fun i => B i i, fun i => ?_, ?_⟩
    · have h := hB (i, i)
      simp only [Interval.diag, Entrywise.entry_mat, Matrix.diagonal_apply_eq] at h
      exact h
    · ext i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  · rintro ⟨x, hx, rfl⟩ ⟨i, j⟩
    by_cases hij : i = j
    · subst hij
      simp only [Interval.diag, Entrywise.entry_mat, Matrix.diagonal_apply_eq]
      exact hx i
    · simp [Interval.diag, Matrix.diagonal_apply_ne _ hij]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
