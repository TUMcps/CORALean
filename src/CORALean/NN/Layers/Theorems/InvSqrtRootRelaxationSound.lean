module

public import CORALean.NN.Layers.Operations.InvSqrtRootRelaxation
public import CORALean.NN.Layers.Theorems.OfAntitoneSound
public import CORALean.NN.Layers.Theorems.Real.AntitoneInvSqrt

@[expose] public section

/-!
# The inverse square root relaxation (machine) is sound

The clamp `max a 1` is exact and the root at least `1`, so the divisors are positive:
`sqrtUp` in the divisor of the lower end, `sqrtDown` floored at `1` in the divisor of the upper end.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrtRootRelaxation_sound (p : ℕ) :
    (invSqrtRootRelaxation (𝕋 := 𝕋) p).Sound Real.invSqrt := by -- --- PROOF ---
  refine Relaxation.ofAntitone_sound Real.antitone_invSqrt ⟨fun a => ?_, fun a => ?_⟩
  · -- lower end: the divisor is above the root, which is at least `1`
    have hm : toReal (maximum a one) = max (toReal a) 1 := by rw [toReal_maximum, toReal_one]
    have hup := le_sqrtUp p (maximum a one)
    rw [hm] at hup
    have h1 : 1 ≤ Real.sqrt (max (toReal a) 1) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; simp
    have hs : 0 < toReal (sqrtUp p (maximum a one)) := by linarith
    refine le_trans (divDown_le_div _ _ hs) ?_
    rw [toReal_one, Real.invSqrt, inv_eq_one_div]
    exact one_div_le_one_div_of_le (lt_of_lt_of_le one_pos h1) hup
  · -- upper end: the divisor is below the root, and at least `1`
    have hm : toReal (maximum a one) = max (toReal a) 1 := by rw [toReal_maximum, toReal_one]
    have hdn := sqrtDown_le p (maximum a one)
    rw [hm] at hdn
    have h1 : 1 ≤ Real.sqrt (max (toReal a) 1) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; simp
    have hd : toReal (maximum one (sqrtDown p (maximum a one))) ≤ Real.sqrt (max (toReal a) 1) := by
      rw [toReal_maximum, toReal_one]; exact max_le h1 hdn
    have hd1 : 1 ≤ toReal (maximum one (sqrtDown p (maximum a one))) := by
      rw [toReal_maximum, toReal_one]; exact le_max_left _ _
    refine le_trans ?_ (div_le_divUp _ _ (lt_of_lt_of_le one_pos hd1))
    rw [toReal_one, Real.invSqrt, inv_eq_one_div]
    exact one_div_le_one_div_of_le (lt_of_lt_of_le one_pos hd1) hd

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
