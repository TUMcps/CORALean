import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The Taylor coefficients of `1/x`

`(1/x)⁽ᵏ⁾(c)/k! = (-1)ᵏ/cᵏ⁺¹`, from `iter_deriv_inv`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.inv_coef (c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => x⁻¹) c / (k.factorial : ℝ) = (-1) ^ k / c ^ (k + 1) := by
  rw [iteratedDeriv_eq_iterate, show (fun x : ℝ => x⁻¹) = Inv.inv from rfl, iter_deriv_inv]
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
