module

public import CORALean.ContSet.Interval.Float.Operations.InfNorm
public import CORALean.ContSet.Interval.Float.Theorems.MagnitudeMatEqAbsMax
public import CORALean.ContSet.Interval.Real.Operations.InfNorm

@[expose] public section

/-!
# `Interval.infNorm` bounds the exact layer's `infNorm`

The larger end in absolute value is exact, so the row sums of `magnitudeMat` are the real ones up
to the upward rounding of the sums, and the maximum does not fall below them.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* the exact layer's infinity norm is at most the float one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.infNorm_le (I : Interval (Mat 𝕋 m n)) : -- --- CONCL ---
    Real.Interval.infNorm I.nominal ≤ toReal I.infNorm := by -- --- PROOF ---
  -- the stored larger ends are the exact layer's `absMax`
  have hA : ∀ i j, I.nominal.absMax i j = toReal (I.magnitudeMat i j) := fun i j =>
    congrFun (congrFun I.magnitudeMat_eq_absMax.symm i) j
  have h0 : ∀ i j, 0 ≤ toReal (I.magnitudeMat i j) := fun i j => by
    rw [← hA]
    exact le_max_of_le_left (abs_nonneg _)
  -- the supremum over rows is bounded by `maximumOver` of the rounded row sums
  show (⨆ i, ∑ j, |I.nominal.absMax i j|) ≤ toReal (maximumOver fun i => sumUp fun j =>
    I.magnitudeMat i j)
  rcases isEmpty_or_nonempty (Fin m) with h | h
  · rw [Real.iSup_of_isEmpty]
    have : m = 0 := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exact h0
      · exact absurd ⟨⟨0, h0⟩⟩ (not_nonempty_iff.mpr h)
    subst this
    rw [maximumOver, toReal_zero]
  · refine ciSup_le fun i => ?_
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      (le_trans (sum_le_sumUp fun j => I.magnitudeMat i j)
        (le_maximumOver (fun i => sumUp fun j => I.magnitudeMat i j) i))
    rw [hA, abs_of_nonneg (h0 i j)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
