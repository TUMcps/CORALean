import CORALean.NN.Layers.Operations.LipConstrScaleFloat
import CORALean.NN.Layers.Operations.LipConstrScale

/-!
# The float scaling box contains the exact scaling

For `0 < λ`, the diagonal of `N` that `Layer.lipConstrScale` computes at the weights and
`λ` the floats denote lies in `Layer.lipConstrScaleFloat`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.lipConstrScaleFloat_mem (W : Mat 𝕋 m n) (lam : 𝕋) (hl : 0 < toReal lam) :
    Layer.lipConstrScale (toRealMat W) (toReal lam)
      ∈ (Layer.lipConstrScaleFloat W lam).construct := by -- --- PROOF ---
  intro i
  -- the row sum is bracketed by the two rounded sums
  set s : ℝ := ∑ j, |toReal (W i j)| with hs
  have hrad : s ≤ toReal (radius W i) := sum_abs_le_radius i
  have hdn : toReal (sumDown fun j => absolute (W i j)) ≤ s := by
    refine le_trans (sumDown_le_sum _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => toReal_absolute _
  -- hence `λ⁻¹ s` is bracketed by the two rounded quotients
  have hD : Layer.lipConstrScale (toRealMat W) (toReal lam) i
      = 1 / max 1 ((toReal lam)⁻¹ * s) := rfl
  have hup : (toReal lam)⁻¹ * s ≤ toReal (divUp (radius W i) lam) := by
    rw [inv_mul_eq_div]
    refine le_trans ?_ (div_le_divUp _ _ hl)
    exact div_le_div_of_nonneg_right hrad hl.le
  have hdown : toReal (divDown (sumDown fun j => absolute (W i j)) lam) ≤ (toReal lam)⁻¹ * s := by
    rw [inv_mul_eq_div]
    exact le_trans (divDown_le_div _ _ hl) (div_le_div_of_nonneg_right hdn hl.le)
  -- and the divisor, which is at least `1`, by their maxima with `1`
  have h1hi : (1 : ℝ) ≤ toReal (maximum one (divUp (radius W i) lam)) := by
    rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have h1lo : (1 : ℝ) ≤ toReal (maximum one
      (divDown (sumDown fun j => absolute (W i j)) lam)) := by
    rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have hDhi : max 1 ((toReal lam)⁻¹ * s) ≤ toReal (maximum one (divUp (radius W i) lam)) := by
    rw [toReal_maximum, toReal_one]; exact max_le_max le_rfl hup
  have hDlo : toReal (maximum one (divDown (sumDown fun j => absolute (W i j)) lam))
      ≤ max 1 ((toReal lam)⁻¹ * s) := by
    rw [toReal_maximum, toReal_one]; exact max_le_max le_rfl hdown
  have hpos : (0 : ℝ) < max 1 ((toReal lam)⁻¹ * s) := lt_of_lt_of_le one_pos (le_max_left _ _)
  -- the reciprocal of a bracketed positive divisor is bracketed by the rounded reciprocals
  show toReal (divDown one (maximum one (divUp (radius W i) lam)))
      ≤ Layer.lipConstrScale (toRealMat W) (toReal lam) i ∧
    Layer.lipConstrScale (toRealMat W) (toReal lam) i
      ≤ toReal (divUp one (maximum one (divDown (sumDown fun j => absolute (W i j)) lam)))
  rw [hD]
  constructor
  · refine le_trans (divDown_le_div _ _ (lt_of_lt_of_le one_pos h1hi)) ?_
    rw [toReal_one]
    exact one_div_le_one_div_of_le hpos hDhi
  · refine le_trans ?_ (div_le_divUp _ _ (lt_of_lt_of_le one_pos h1lo))
    rw [toReal_one]
    exact one_div_le_one_div_of_le (lt_of_lt_of_le one_pos h1lo) hDlo

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
