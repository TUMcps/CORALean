module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# The variation-of-constants formula, as a function of time

`e^{tA} x_0 + ∫₀ᵗ e^{(t-s)A} u(s) ds`: what `eq_closedForm_of_flow` proves every
`IsTrajectory` equals, and what `ClosedFormFlow` proves satisfies the integral
equation `IsTrajectory.flow` asks for, for *any* measurable bounded `u`. Named
apart from either use: `Theorems/ClosedFormFlow.lean` and the `⊇` half of
`reachSet_eq` both build on it, at a point rather than a run.
-/

-- Authors:       Claude Sonnet 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The variation-of-constants formula at time `t`, for an initial point `x0`
and an input `u`, without requiring `u` to be the input of any `IsTrajectory`. -/
noncomputable def LinearSys.closedForm (sys : LinearSys 𝕋 n) (x0 : Vec ℝ n) (u : ℝ → Vec ℝ n)
    (t : ℝ) : Vec ℝ n :=
  exp (t • toRealMat sys.A) *ᵥ x0 + ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
