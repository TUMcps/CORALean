module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CORALean.Global.Tensor

@[expose] public section

/-!
# The integration step of Wang and Ye's Theorem 5.2 fails for a positive exponent

[1, Thm. 5.2] integrates the decay bound `|h(t)| ≤ Ce^{-t z̃}` (5.2) against the a posteriori
bound (3.6): `∫₀^τ e^{-t z̃}dt = e^{-τz̃}(e^{τz̃} - 1)/z̃ ≤ τe^{-τz̃}`, "where we have used
`(e^x - 1)/x ≤ 1` for any `x ≠ 0`". That holds for `x < 0` only: `(e^x - 1)/x > 1` for `x > 0`,
and `z̃ > 0` is the case of interest (a positive definite `A`, Cor. 5.3). At `z̃ = 1`, `τ = 1`:
`∫₀¹e^{-t}dt = 1 - e^{-1} > e^{-1}`. The printed bound (5.4) itself is not refuted: it follows
from the weighted bound of the proof of Thm. 3.1 (`Krylov.error_le_of_decay_bound`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the integral bound fails for some positive exponent and step

## References

* [1] H. Wang, Q. Ye. "Error bounds for the Krylov subspace methods for computations of matrix
  exponentials". SIAM Journal on Matrix Analysis and Applications, 38(1):155-187, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 5.2]'s step `∫₀^τ e^{-t z̃}dt ≤ τe^{-τz̃}` fails at `z̃ = τ = 1`. -/
theorem Krylov.wang_ye_integral_step_counterexample : -- --- CONCL ---
    ∃ z τ : ℝ, 0 < z ∧ 0 < τ ∧
      τ * Real.exp (-(τ * z)) < ∫ s in (0 : ℝ)..τ, Real.exp (-(s * z)) := by -- --- PROOF ---
  -- at `z = τ = 1` the integral is `1 - e^{-1}`
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  have h : ∫ s in (0 : ℝ)..1, Real.exp (-(s * 1)) = 1 - Real.exp (-1) := by
    simp only [mul_one]
    rw [intervalIntegral.integral_comp_neg (fun x => Real.exp x)]
    simp
  rw [h]
  -- and `e^{-1} < 1/2` as `e > 2`
  have he : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  have h1 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h2 : (Real.exp 1)⁻¹ < 1 / 2 := by
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    simpa using he
  simp only [one_mul, mul_one]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
