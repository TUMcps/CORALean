import CORALean.ContSet.Taylm.Real.Operations.Log
import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter

/-!
# `Taylm.log` encloses `log ∘ f`

Where the range and the centre are positive, CORA's domain check: there `log` is smooth on
the whole hull, and `log⁽ᴺ⁺¹⁾ = (x⁻¹)⁽ᴺ⁾` is `iter_deriv_inv`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.log_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hpos : 0 < min T.constCoef T.bounds.1) :
    T.log.Encloses fun t => Real.log (f t) := by -- --- PROOF ---
  refine Taylm.taylor_outer h _ _ _ (fun ξ hξ => Real.contDiffAt_log.2
    (ne_of_gt (lt_of_lt_of_le hpos hξ.1))) fun ξ hξ => ?_
  have hξ0 : 0 < ξ := lt_of_lt_of_le hpos hξ.1
  -- `|(-1)ᴺ N! ξ⁻ᴺ⁻¹| = N! / ξᴺ⁺¹`, decreasing in `ξ`
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv,
    abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
    show (-1 - (T.maxOrder : ℤ)) = -((T.maxOrder + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, abs_inv, abs_pow, abs_of_pos hξ0, div_eq_mul_inv]
  gcongr
  exact hξ.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
