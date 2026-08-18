import CORALean.Arithmetic.Float.ContSet.Interval.API

/-!
# `Interval.mtimes` encloses the exact image

Termwise the rounded products enclose the exact ones, and `minimum`/`maximum`
are exact, so both layers pick the same endpoint; `sumDown`/`sumUp` then enclose
the sum.

The sign of `M i k` is never examined. That case split lives once, in
`Arithmetic.Real`, and is reached through `mtimes_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.Interval.Proofs

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

theorem mtimes_outer_refines (M : Mat 𝕋 m n) (I : Interval 𝕋 n) :
    (Real.Interval.mtimes (toRealMat M) I.nominal).construct ⊆
      (Interval.mtimes M I).construct := by
  intro x hx i
  -- the exact bound has to be a visible sum before it can be compared termwise
  have h := hx i
  simp only [Real.Interval.mtimes, toRealMat, Interval.nominal, toRealVec] at h
  have hinf : ∀ k, toReal (minimum (mulDown (M i k) (I.inf k)) (mulDown (M i k) (I.sup k)))
      ≤ min (toReal (M i k) * toReal (I.inf k)) (toReal (M i k) * toReal (I.sup k)) := by
    intro k
    rw [toReal_minimum]
    exact min_le_min (mulDown_le_mul _ _) (mulDown_le_mul _ _)
  have hsup : ∀ k, max (toReal (M i k) * toReal (I.inf k)) (toReal (M i k) * toReal (I.sup k))
      ≤ toReal (maximum (mulUp (M i k) (I.inf k)) (mulUp (M i k) (I.sup k))) := by
    intro k
    rw [toReal_maximum]
    exact max_le_max (mul_le_mulUp _ _) (mul_le_mulUp _ _)
  exact ⟨le_trans (sumDown_le_sum _) (le_trans (Finset.sum_le_sum fun k _ => hinf k) h.1),
         le_trans h.2 (le_trans (Finset.sum_le_sum fun k _ => hsup k) (sum_le_sumUp _))⟩

end CORALean.Arithmetic.Float.Interval.Proofs
