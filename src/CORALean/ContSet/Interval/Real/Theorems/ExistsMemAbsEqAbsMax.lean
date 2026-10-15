module

public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# A nonempty box has a member with the absolute values of `absMax`

In every entry the endpoint of larger magnitude is a member of that entry's interval, and the
box is the product of its entries, so one matrix takes all of them at once. Every norm that
depends on the absolute values of the entries alone is therefore attained at it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The corner of larger magnitude in every entry has the absolute values `absMax`. -/
theorem Interval.exists_mem_abs_eq_absMax (A : Interval (Mat ℝ m n))
    (hA : ∀ p q, A.inf p q ≤ A.sup p q) :
    ∃ M ∈ A.construct, ∀ i j, |M i j| = A.absMax i j := by -- --- PROOF ---
  classical
  refine ⟨Matrix.of fun p q => if |A.inf p q| ≤ |A.sup p q| then A.sup p q else A.inf p q,
    Interval.mem_mat_iff.mpr fun p q => ?_, fun i j => ?_⟩
  · simp only [Matrix.of_apply]
    split_ifs
    · exact ⟨hA p q, le_rfl⟩
    · exact ⟨le_rfl, hA p q⟩
  · simp only [Matrix.of_apply, Interval.absMax]
    split_ifs with h
    · rw [max_eq_right h]
    · rw [max_eq_left (not_le.mp h).le]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
