module

public import CORALean.ContSet.Interval.Float.Operations.SplitAt
public import CORALean.ContSet.Interval.Real.Theorems.SplitAtCover

@[expose] public section

/-!
# `Interval.splitAt` covers the box it bisects

The first half reaches the midpoint rounded up and the second starts at it rounded down, and the
first is never below the second, so a point's `j`-th coordinate is on one side of one of them.
A cover and not a partition, as over ℝ; and the halves may overlap by the rounding.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.splitAt_cover (I : Interval (Vec 𝕋 n)) (j : Fin n) :
    I.construct ⊆ (I.splitAt j).1.construct ∪ (I.splitAt j).2.construct := by -- --- PROOF ---
  intro x hx
  -- the rounded-down midpoint is at most the rounded-up one
  have hlo : toReal (half (addDown (I.inf j) (I.sup j))) ≤
      toReal (half (addUp (I.inf j) (I.sup j))) := by
    rw [toReal_half, toReal_half]
    linarith [addDown_le_add (I.inf j) (I.sup j), add_le_addUp (I.inf j) (I.sup j)]
  unfold Interval.splitAt
  -- a point is on the lower side of the lower midpoint, or on the upper side of it
  rcases le_total (x j) (toReal (half (addDown (I.inf j) (I.sup j)))) with h | h
  · refine Or.inl fun i => ⟨(hx i).1, ?_⟩
    by_cases hij : i = j
    · -- the bisected coordinate: below the lower midpoint, hence below the upper
      subst hij
      show x i ≤ toReal (Function.update I.sup i _ i)
      rw [Function.update_self]
      exact le_trans h hlo
    · -- every other coordinate keeps its bound
      show x i ≤ toReal (Function.update I.sup j _ i)
      rw [Function.update_of_ne hij]
      exact (hx i).2
  · refine Or.inr fun i => ⟨?_, (hx i).2⟩
    by_cases hij : i = j
    · -- the bisected coordinate: above the lower midpoint, which is the second half's bound
      subst hij
      show toReal (Function.update I.inf i _ i) ≤ x i
      rw [Function.update_self]
      exact h
    · -- every other coordinate keeps its bound
      show toReal (Function.update I.inf j _ i) ≤ x i
      rw [Function.update_of_ne hij]
      exact (hx i).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
