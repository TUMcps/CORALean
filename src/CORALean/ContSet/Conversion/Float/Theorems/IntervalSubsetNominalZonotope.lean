module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalReaches
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# A box as a zonotope, over a floating-point scalar: `subset_nominal_zonotope`

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* interval is contained in the nominal zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The generators alone already cover the box, before the error box is even
consulted — which is what lets a caller read off coefficients directly. -/
theorem Interval.subset_nominal_zonotope (I : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    I.construct ⊆ InflatedContSet.nominalSet I.zonotope := by -- --- PROOF ---
  intro x hx
  have hlo : ∀ i, toReal (I.inf i) ≤ x i := fun i => (hx i).1
  have hhi : ∀ i, x i ≤ toReal (I.sup i) := fun i => (hx i).2
  have hreach : ∀ i, toReal (I.center i) - toReal (I.radiusFrom i) ≤ x i
      ∧ x i ≤ toReal (I.center i) + toReal (I.radiusFrom i) := fun i =>
    ⟨le_trans (I.reaches i).1 (hlo i), le_trans (hhi i) (I.reaches i).2⟩
  -- the coefficient a coordinate needs, zero where the box has no width there
  refine ⟨fun i => if toReal (I.radiusFrom i) = 0 then 0
      else (x i - toReal (I.center i)) / toReal (I.radiusFrom i), fun i => ?_, ?_⟩
  · by_cases h : toReal (I.radiusFrom i) = 0
    · simp only [if_pos h, abs_zero]
      norm_num
    · have hpos : 0 < toReal (I.radiusFrom i) :=
        lt_of_le_of_ne (by linarith [(hreach i).1, (hreach i).2]) (Ne.symm h)
      simp only [if_neg h]
      rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
      constructor <;> linarith [(hreach i).1, (hreach i).2]
  -- the value: only the diagonal entry `i` reaches coordinate `i`
  · funext i
    have hsum : (∑ j : Fin n, (if toReal (I.radiusFrom j) = 0 then (0:ℝ)
          else (x j - toReal (I.center j)) / toReal (I.radiusFrom j)) •
            (fun i => toReal (diagonalBlock I.radiusFrom j i) : Vec ℝ n)) i
        = (if toReal (I.radiusFrom i) = 0 then (0:ℝ)
            else (x i - toReal (I.center i)) / toReal (I.radiusFrom i))
          * toReal (I.radiusFrom i) := by
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [toReal_diagonalBlock, Matrix.diagonal_apply_eq, toRealVec]
      · intro j _ hj
        simp [toReal_diagonalBlock, Matrix.diagonal_apply_ne _ hj]
      · intro hc
        exact absurd (Finset.mem_univ i) hc
    -- the goal spelled out, so `hsum` matches it
    show x i = ((fun i => toReal (I.center i) : Vec ℝ n)
      + ∑ j : Fin n, (if toReal (I.radiusFrom j) = 0 then (0:ℝ)
        else (x j - toReal (I.center j)) / toReal (I.radiusFrom j)) •
          (fun i => toReal (diagonalBlock I.radiusFrom j i) : Vec ℝ n)) i
    rw [Pi.add_apply, hsum]
    by_cases h : toReal (I.radiusFrom i) = 0
    · rw [if_pos h, zero_mul, add_zero]
      have h₁ := (hreach i).1
      have h₂ := (hreach i).2
      rw [h] at h₁ h₂
      linarith
    · rw [if_neg h, div_mul_cancel₀ _ h]
      ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
