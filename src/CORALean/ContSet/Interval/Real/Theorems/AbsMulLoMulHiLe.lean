module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# The product of two intervals is as small as their magnitudes

Every corner of `[a, b]·[c, d]` is at most `M·R` in magnitude when the ends of the first are at
most `M` and those of the second at most `R`, so the least and the greatest corner are too.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.abs_mulLo_mulHi_le {a b c d M R : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M)
    (hc : |c| ≤ R) (hd : |d| ≤ R) :
    |Interval.mulLo a b c d| ≤ M * R ∧ |Interval.mulHi a b c d| ≤ M * R := by -- --- PROOF ---
  have k : ∀ x y, |x| ≤ M → |y| ≤ R → |x * y| ≤ M * R := fun x y hx hy => by
    rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)
  have h1 := k a c ha hc; have h2 := k a d ha hd; have h3 := k b c hb hc; have h4 := k b d hb hd
  rw [abs_le] at h1 h2 h3 h4
  unfold Interval.mulLo Interval.mulHi
  -- each end is one of the four corners
  constructor <;> rw [abs_le] <;> constructor <;>
    simp only [le_min_iff, min_le_iff, le_max_iff, max_le_iff] <;>
    first | (refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith) | (left; left; linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
