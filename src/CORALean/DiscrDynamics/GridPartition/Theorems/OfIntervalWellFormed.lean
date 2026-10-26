module

public import CORALean.DiscrDynamics.GridPartition.Operations.OfInterval
public import CORALean.DiscrDynamics.GridPartition.Definitions.Basic

@[expose] public section

/-!
# `partition(I, segs)` is well formed

The evenly spaced dividers of a nonempty box do not decrease.

## Inputs
* `I` – box
* `segs` – segments per dimension

## Hypotheses
* `h` – every segment count positive
* `hI` – box nonempty

## Conclusion
* the evenly cut partition is well formed
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An evenly cut nonempty box with every dimension cut is a well-formed partition. -/
theorem GridPartition.ofInterval_isWellFormed (I : Real.Interval (Vec ℝ n)) {segs : Fin n → ℕ}
    (h : ∀ j, 0 < segs j) (hI : ∀ j, I.inf j ≤ I.sup j) : -- --- CONCL ---
    (GridPartition.ofInterval I segs).IsWellFormed := by -- --- PROOF ---
  intro j
  refine ⟨h j, fun a b hab hb => ?_⟩
  have hm : (0 : ℝ) < segs j := by exact_mod_cast h j
  have hstep : 0 ≤ (I.sup j - I.inf j) / segs j := div_nonneg (by linarith [hI j]) hm.le
  have hb' : b ≤ segs j := hb
  simp only [GridPartition.ofInterval]
  by_cases hbm : b = segs j
  · by_cases ham : a = segs j
    · simp [hbm, ham]
    · -- the last divider is `sup`, the others are below it
      rw [if_pos hbm, if_neg ham]
      have ha : (a : ℝ) ≤ segs j := by exact_mod_cast (by omega : a ≤ segs j)
      have : (a : ℝ) * ((I.sup j - I.inf j) / segs j) ≤
          segs j * ((I.sup j - I.inf j) / segs j) := mul_le_mul_of_nonneg_right ha hstep
      have h2 : (segs j : ℝ) * ((I.sup j - I.inf j) / segs j) = I.sup j - I.inf j := by
        field_simp
      linarith
  · have ham : a ≠ segs j := by omega
    rw [if_neg hbm, if_neg ham]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    have := mul_le_mul_of_nonneg_right this hstep
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
