module

public import CORALean.ContSet.Interval.Float.Operations.MatNorm
public import CORALean.ContSet.Interval.Float.Theorems.CenterMemCenterBoxMat
public import CORALean.ContSet.Interval.Float.Theorems.RadiusMatGe
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Operations.MatNorm

@[expose] public section

/-!
# `Interval.matNorm` bounds the norm of every member

Each member's entry is within the rounded `abs(center) + rad` in absolute value, because the
center is bracketed and the half-width rounds up; the column sums, row sums and sum of squares
then round up, and the maximum and `sqrtUp` do not fall below them.

## Inputs
* `steps` – number of Newton steps of the square root
* `p` – norm type
* `I` – interval matrix
* `M` – member matrix

## Hypotheses
* `hM` – `M` lies in the interval matrix

## Conclusion
* the norm of `M` is at most the float norm
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

theorem Interval.matNorm_le (steps : ℕ) (p : Real.Interval.NormType) (I : Interval (Mat 𝕋 m n))
    {M : Mat ℝ m n} (hM : M ∈ I.construct) : -- --- CONCL ---
    p.eval M ≤ toReal (I.matNorm steps p) := by -- --- PROOF ---
  -- the center is bracketed, the member lies between the bounds
  have hc := Interval.mem_mat_iff.mp (Interval.center_mem_centerBoxMat I)
  have hMi := Interval.mem_mat_iff.mp hM
  -- every entry is below the rounded `abs(center) + rad` in absolute value
  have hb : ∀ i j, |M i j| ≤ toReal (I.step_normEntry i j) := by
    intro i j
    -- the member is within the radius of the real center
    have h1 : |M i j| ≤ |I.nominal.center i j| + I.nominal.radius i j := by
      have hrad : I.nominal.radius i j = (toReal (I.sup i j) - toReal (I.inf i j)) / 2 := by
        show (2:ℝ)⁻¹ * (toReal (I.sup i j) - toReal (I.inf i j)) = _
        ring
      have hcen : I.nominal.center i j = (toReal (I.inf i j) + toReal (I.sup i j)) / 2 := by
        show (2:ℝ)⁻¹ * (toReal (I.inf i j) + toReal (I.sup i j)) = _
        ring
      rw [hrad, hcen]
      have := hMi i j
      rw [abs_le]
      constructor <;>
        cases abs_cases ((toReal (I.inf i j) + toReal (I.sup i j)) / 2) <;>
          linarith [this.1, this.2]
    -- the center's absolute value is below the larger end of its bracket
    refine le_trans h1 ?_
    have h2 : |I.nominal.center i j| ≤ toReal (maximum (absolute (I.centerBoxMat.inf i j))
        (absolute (I.centerBoxMat.sup i j))) := by
      rw [toReal_maximum, toReal_absolute, toReal_absolute]
      exact abs_le_max_abs_abs (hc i j).1 (hc i j).2
    have h3 := Interval.radiusMat_ge I i j
    exact le_trans (add_le_add h2 h3) (add_le_addUp _ _)
  have h0 : ∀ i j, 0 ≤ toReal (I.step_normEntry i j) := fun i j => le_trans (abs_nonneg _) (hb i j)
  -- then each norm type adds up the bounds on the entries and rounds the sums up
  cases p with
  | one =>
    show (⨆ j, ∑ i, |M i j|) ≤ toReal (maximumOver fun j => sumUp fun i => I.step_normEntry i j)
    -- the supremum over no column is `0`, as is `maximumOver` of none
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · rw [Real.iSup_of_isEmpty]
      have : n = 0 := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · exact h0
        · exact absurd ⟨⟨0, h0⟩⟩ (not_nonempty_iff.mpr h)
      subst this
      rw [maximumOver, toReal_zero]
    · refine ciSup_le fun j => ?_
      exact le_trans (Finset.sum_le_sum fun i _ => hb i j)
        (le_trans (sum_le_sumUp fun i => I.step_normEntry i j)
          (le_maximumOver (fun j => sumUp fun i => I.step_normEntry i j) j))
  | inf =>
    show (⨆ i, ∑ j, |M i j|) ≤ toReal (maximumOver fun i => sumUp fun j => I.step_normEntry i j)
    -- the supremum over no row is `0`, as is `maximumOver` of none
    rcases isEmpty_or_nonempty (Fin m) with h | h
    · rw [Real.iSup_of_isEmpty]
      have : m = 0 := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exact h0
        · exact absurd ⟨⟨0, h0⟩⟩ (not_nonempty_iff.mpr h)
      subst this
      rw [maximumOver, toReal_zero]
    · refine ciSup_le fun i => ?_
      exact le_trans (Finset.sum_le_sum fun j _ => hb i j)
        (le_trans (sum_le_sumUp fun j => I.step_normEntry i j)
          (le_maximumOver (fun i => sumUp fun j => I.step_normEntry i j) i))
  | fro =>
    show Real.sqrt (∑ i, ∑ j, M i j ^ 2) ≤ toReal (sqrtUp steps (sumUp fun i => sumUp fun j =>
      mulUp (I.step_normEntry i j) (I.step_normEntry i j)))
    -- the sum of squares is below the rounded one, and `sqrtUp` is above the root
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_sqrtUp steps _)
    refine le_trans ?_ (sum_le_sumUp _)
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
    rw [← sq_abs (M i j)]
    calc |M i j| ^ 2 = |M i j| * |M i j| := pow_two _
      _ ≤ toReal (I.step_normEntry i j) * toReal (I.step_normEntry i j) :=
        mul_le_mul (hb i j) (hb i j) (abs_nonneg _) (h0 i j)
      _ ≤ _ := mul_le_mulUp _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
