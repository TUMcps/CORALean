import CORALean.ContSet.Taylm.Float.Operations.InvBound
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The derivative bound of `1/x` holds

Wherever `|ξ|` is at least the positive `m`, `|(1/x)⁽ᴺ⁺¹⁾ ξ| = (N+1)! / |ξ|ᴺ⁺²` is at most
`(N+1)! · (1/m)ᴺ⁺²`, which `invBound` rounds up factor by factor.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.invBound_ge (m : 𝕋) (hm : 0 < toReal m) (N : ℕ) {ξ : ℝ} (hξ : toReal m ≤ |ξ|) :
    |iteratedDeriv (N + 1) (fun x : ℝ => x⁻¹) ξ| ≤
      toReal (Taylm.invBound m N) := by -- --- PROOF ---
  have hξ0 : 0 < |ξ| := lt_of_lt_of_le hm hξ
  -- `|ξ⁻¹ ^ (N+2)|` with its factorial, as the product the bound rounds
  rw [iteratedDeriv_eq_iterate, show (fun x : ℝ => x⁻¹) = Inv.inv from rfl, iter_deriv_inv,
    abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
    show (-1 - ((N + 1 : ℕ) : ℤ)) = -((N + 2 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, abs_inv, abs_pow, ← one_div, ← one_div_pow]
  -- the three factors
  have hI := (intDown_le_intUp (𝕋 := 𝕋) ((N + 1).factorial : ℤ)).2
  have hdiv := div_le_divUp (one : 𝕋) m hm
  rw [toReal_one] at hdiv
  have h1 : 1 / |ξ| ≤ 1 / toReal m := one_div_le_one_div_of_le hm hξ
  have hc := le_powUp (by positivity : (0 : ℝ) ≤ 1 / |ξ|) (le_trans h1 hdiv) (N + 2)
  refine le_trans ?_ (mul_le_mulUp _ _)
  push_cast at hI
  exact mul_le_mul hI hc (by positivity) (le_trans (Nat.cast_nonneg _) hI)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
