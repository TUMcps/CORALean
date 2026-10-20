module

public import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# The closed form with the exponential outside the integral

`e^{ρA} x₀ + ∫₀^ρ e^{(ρ-s)A} u(s) ds` as `e^{ρA}(x₀ + ∫₀^ρ e^{-sA} u(s) ds)`: the
substituted primitive is what both `closedForm_continuousOn` and
`variation_of_constants` read off, the first for its continuity in `ρ`, the
second to cancel `e^{ρA}` against `e^{-ρA}`.

## Inputs
* `sys` – linear system
* `x0` – initial point
* `u` – input signal
* `ρ` – time

## Hypotheses
* `hint` – integrand interval integrable

## Conclusion
* the closed form has the exponential outside the integral
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exponential moved outside the integral: `closedForm` as `e^{ρA}` applied
to the substituted primitive, the shape whose continuity does not need `u`'s. -/
theorem LinearSys.closedForm_eq (sys : LinearSys 𝕋 n) (x0 : Vec ℝ n) (u : ℝ → Vec ℝ n) {ρ : ℝ}
    (hint : IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume 0 ρ) :
    sys.closedForm x0 u ρ
      = exp (ρ • toRealMat sys.A) *ᵥ
          (x0 + ∫ s in (0:ℝ)..ρ, exp ((-s) • toRealMat sys.A) *ᵥ u s) := by -- --- PROOF ---
  set A := toRealMat sys.A
  have hmul : ∀ c d : ℝ, exp (c • A) * exp (d • A) = exp ((c + d) • A) := by
    intro c d
    have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
    rw [add_smul]; exact (exp_add_of_commute hc).symm
  have key : mulVecL (exp (ρ • A)) (∫ s in (0:ℝ)..ρ, exp ((-s) • A) *ᵥ u s)
      = ∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show exp (ρ • A) *ᵥ (exp ((-s) • A) *ᵥ u s) = exp ((ρ - s) • A) *ᵥ u s
    rw [Matrix.mulVec_mulVec]
    congr 2
    rw [sub_eq_add_neg, ← hmul]
  show exp (ρ • A) *ᵥ x0 + ∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s
    = exp (ρ • A) *ᵥ (x0 + ∫ s in (0:ℝ)..ρ, exp ((-s) • A) *ᵥ u s)
  rw [Matrix.mulVec_add, ← key]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
