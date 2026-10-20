module

public import CORALean.ContSet.Interval.Float.Operations.Atan2Hi
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqArctanOfRePos
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqPiDivTwoSubArctanOfImPos
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqNegPiDivTwoSubArctanOfImNeg

@[expose] public section

/-!
# `Interval.atan2Hi` is an upper bound

The corner value `atan2Hi p k a b` is at least the argument of `a + b i`, whichever half-plane
holds it: in each certified half-plane through the monotonicity of `arctan` and the rounded
quotients, and `π` above every argument.

## Inputs
* `p` – halving count
* `k` – bisection and Newton steps
* `a` – abscissa
* `b` – ordinate

## Hypotheses
* none

## Conclusion
* the argument of `a + b i` is below the upper bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.le_atan2Hi (p k : ℕ) (a b : 𝕋) : -- --- CONCL ---
    Complex.arg ⟨toReal a, toReal b⟩ ≤ toReal (Interval.atan2Hi p k a b) := by -- --- PROOF ---
  have hpm : toReal (acosDown p k (zero : 𝕋)) ≤ Real.pi / 2 := by
    have := acosDown_le p k (zero : 𝕋)
    rwa [toReal_zero, Real.arccos_zero] at this
  have hpp : Real.pi / 2 ≤ toReal (acosUp p k (zero : 𝕋)) := by
    have := le_acosUp p k (zero : 𝕋)
    rwa [toReal_zero, Real.arccos_zero] at this
  have hm := Real.arctan_strictMono.monotone
  unfold Interval.atan2Hi
  dsimp only
  split_ifs with h1 h2 h3
  · -- right half-plane
    have ha : 0 < toReal a := by simpa [toReal_zero] using toReal_lt_of_ltStrict h1
    rw [Real.arg_eq_arctan_of_re_pos (z := ⟨toReal a, toReal b⟩) ha]
    exact le_trans (hm (div_le_divUp b a ha)) (le_atanUp p k _)
  · -- upper half-plane
    have hb : 0 < toReal b := by simpa [toReal_zero] using toReal_lt_of_ltStrict h2
    rw [Real.arg_eq_pi_div_two_sub_arctan_of_im_pos (z := ⟨toReal a, toReal b⟩) hb]
    have h5 := le_trans (atanDown_le p k (divDown a b)) (hm (divDown_le_div a b hb))
    have h6 := sub_le_subUp (acosUp p k (zero : 𝕋)) (atanDown p k (divDown a b))
    simp only
    linarith
  · -- lower half-plane
    have hb : toReal b < 0 := by simpa [toReal_zero] using toReal_lt_of_ltStrict h3
    have hnb : 0 < toReal (neg b) := by rw [toReal_neg]; linarith
    have hq : toReal (neg a) / toReal (neg b) = toReal a / toReal b := by
      rw [toReal_neg, toReal_neg, neg_div_neg_eq]
    rw [Real.arg_eq_neg_pi_div_two_sub_arctan_of_im_neg (z := ⟨toReal a, toReal b⟩) hb]
    have h5 := le_trans (atanDown_le p k (divDown (neg a) (neg b)))
      (hm (divDown_le_div (neg a) (neg b) hnb))
    rw [hq] at h5
    have h6 := sub_le_subUp (neg (acosDown p k (zero : 𝕋)))
      (atanDown p k (divDown (neg a) (neg b)))
    rw [toReal_neg] at h6
    simp only
    linarith
  · -- no half-plane certified: below `π`
    have h4 := add_le_addUp (acosUp p k (zero : 𝕋)) (acosUp p k (zero : 𝕋))
    have := Complex.arg_le_pi (⟨toReal a, toReal b⟩ : ℂ)
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
