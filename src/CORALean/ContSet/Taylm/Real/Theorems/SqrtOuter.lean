module

public import CORALean.ContSet.Taylm.Real.Operations.Sqrt
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# `Taylm.sqrt` encloses `sqrt ∘ f`

Where the range and the centre are positive. `√x = x^(1/2)` everywhere in Mathlib, so the
derivatives are `iter_deriv_rpow_const`'s, and a negative power decreases.

[1, Def. 3 (sqrt)]: the result is a Taylor model of `sqrt ∘ f`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sqrt_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hpos : 0 < min T.constCoef T.bounds.1) :
    T.sqrt.Encloses fun t => Real.sqrt (f t) := by -- --- PROOF ---
  refine Taylm.taylor_outer h _ _ _ (fun ξ hξ => Real.contDiffAt_sqrt
    (ne_of_gt (lt_of_lt_of_le hpos hξ.1))) fun ξ hξ => ?_
  have hξ0 : 0 < ξ := lt_of_lt_of_le hpos hξ.1
  have hfun : Real.sqrt = fun x : ℝ => x ^ (1 / 2 : ℝ) := funext Real.sqrt_eq_rpow
  rw [hfun, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hξ0 _)]
  -- the exponent `1/2 - (N+1)` is negative
  have hz : (1 / 2 : ℝ) - ((T.maxOrder + 1 : ℕ) : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ ((T.maxOrder + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos hξ.1 hz) (abs_nonneg _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
