module

public import CORALean.ContSet.Taylm.Real.Operations.InvSqrt
public import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# `Taylm.invSqrt` encloses `1 / sqrt ∘ f`

[1, Def. 3 (1/sqrt)] where, as the source asks, the range and the center are positive. The
derivatives are `iter_deriv_rpow_const`'s; a negative power decreases, so the bottom of the
range bounds them, and `x^(-1/2) = 1/√x` for positive `x`.

## Inputs
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function
* `hpos` – the range stays positive

## Conclusion
* the result encloses the reciprocal square root of the function

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.invSqrt_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hpos : 0 < min T.constCoef T.bounds.inf) : -- --- CONCL ---
    T.invSqrt.Encloses fun t => (Real.sqrt (f t))⁻¹ := by -- --- PROOF ---
  have hE : T.invSqrt.Encloses fun t => f t ^ (-(1 / 2) : ℝ) := by
    refine Taylm.taylor_outer h _ _ _ (fun ξ hξ => Real.contDiffAt_rpow_const_of_ne
      (ne_of_gt (lt_of_lt_of_le hpos hξ.1))) fun ξ hξ => ?_
    have hξ0 : 0 < ξ := lt_of_lt_of_le hpos hξ.1
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hξ0 _)]
    -- the exponent `-1/2 - (N+1)` is negative
    have hz : (-(1 / 2) : ℝ) - ((T.maxOrder + 1 : ℕ) : ℝ) ≤ 0 := by
      have : (0 : ℝ) ≤ ((T.maxOrder + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos hξ.1 hz) (abs_nonneg _)
  intro t ht
  -- on the box `f` is positive, where `x^(-1/2)` is `1/√x`
  have hf : 0 < f t := lt_of_lt_of_le hpos (le_trans (min_le_right _ _)
    (Taylm.bounds_mem h ht).1)
  have hr : (Real.sqrt (f t))⁻¹ = f t ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hf.le]
  simp only [hr]
  exact hE t ht

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
