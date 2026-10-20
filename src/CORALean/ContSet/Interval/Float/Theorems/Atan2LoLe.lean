module

public import CORALean.ContSet.Interval.Float.Operations.Atan2Lo
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqArctanOfRePos
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqPiDivTwoSubArctanOfImPos
public import CORALean.ContSet.Interval.Real.Theorems.ArgEqNegPiDivTwoSubArctanOfImNeg

@[expose] public section

/-!
# `Interval.atan2Lo` is a lower bound

The corner value `atan2Lo p k a b` is at most the argument of `a + b i`, whichever half-plane
holds it: in each certified half-plane through the monotonicity of `arctan` and the rounded
quotients, and `-π` below every argument.

## Inputs
* `p` – halving count
* `k` – bisection and Newton steps
* `a` – abscissa
* `b` – ordinate

## Hypotheses
* none

## Conclusion
* the lower bound is below the argument of `a + b i`
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

theorem Interval.atan2Lo_le (p k : ℕ) (a b : 𝕋) : -- --- CONCL ---
    toReal (Interval.atan2Lo p k a b) ≤ Complex.arg ⟨toReal a, toReal b⟩ := by -- --- PROOF ---
  have hpm : toReal (acosDown p k (zero : 𝕋)) ≤ Real.pi / 2 := by
    have := acosDown_le p k (zero : 𝕋)
    rwa [toReal_zero, Real.arccos_zero] at this
  have hpp : Real.pi / 2 ≤ toReal (acosUp p k (zero : 𝕋)) := by
    have := le_acosUp p k (zero : 𝕋)
    rwa [toReal_zero, Real.arccos_zero] at this
  have hm := Real.arctan_strictMono.monotone
  unfold Interval.atan2Lo
  dsimp only
  split_ifs with h1 h2 h3
  · -- right half-plane
    have ha : 0 < toReal a := by simpa [toReal_zero] using toReal_lt_of_ltStrict h1
    rw [Real.arg_eq_arctan_of_re_pos (z := ⟨toReal a, toReal b⟩) ha]
    exact le_trans (atanDown_le p k _) (hm (divDown_le_div b a ha))
  · -- upper half-plane
    have hb : 0 < toReal b := by simpa [toReal_zero] using toReal_lt_of_ltStrict h2
    rw [Real.arg_eq_pi_div_two_sub_arctan_of_im_pos (z := ⟨toReal a, toReal b⟩) hb]
    have := le_trans (hm (div_le_divUp a b hb)) (le_atanUp p k _)
    have := subDown_le_sub (acosDown p k (zero : 𝕋)) (atanUp p k (divUp a b))
    simp only at *
    linarith
  · -- lower half-plane
    have hb : toReal b < 0 := by simpa [toReal_zero] using toReal_lt_of_ltStrict h3
    have hnb : 0 < toReal (neg b) := by rw [toReal_neg]; linarith
    have hq : toReal (neg a) / toReal (neg b) = toReal a / toReal b := by
      rw [toReal_neg, toReal_neg, neg_div_neg_eq]
    rw [Real.arg_eq_neg_pi_div_two_sub_arctan_of_im_neg (z := ⟨toReal a, toReal b⟩) hb]
    have h5 := le_trans (hm (div_le_divUp (neg a) (neg b) hnb)) (le_atanUp p k _)
    have h6 := subDown_le_sub (neg (acosUp p k (zero : 𝕋))) (atanUp p k (divUp (neg a) (neg b)))
    rw [hq] at h5
    rw [toReal_neg] at h6
    simp only
    linarith
  · -- no half-plane certified: below `-π`
    have h4 := add_le_addUp (acosUp p k (zero : 𝕋)) (acosUp p k (zero : 𝕋))
    rw [toReal_neg]
    have := Complex.neg_pi_lt_arg (⟨toReal a, toReal b⟩ : ℂ)
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
