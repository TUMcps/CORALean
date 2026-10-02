import CORALean.ContDynamics.LinearSys.LinearSys
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Matrix.Normed

/-!
# The variation-of-constants formula, as a function of time

`e^{tA} x_0 + ∫₀ᵗ e^{(t-s)A} u(s) ds`: what `variation_of_constants` proves every
`Trajectory` equals, and what `ClosedFormFlow` proves satisfies the raw
integral equation `IntegralTrajectory.flow` asks for, for *any* measurable
bounded `u` — not only ones a two-sided derivative pins down. Named apart from
either use: `Theorems/ClosedFormFlow.lean` and the `⊇` half of the integral
reachable set both build on it, at a point rather than a run.
-/

-- Authors:       Tobias Ladner
-- Written:       15-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The variation-of-constants formula at time `t`, for an initial point `x0`
and an input `u`, without requiring `u` to be the input of any `Trajectory`. -/
noncomputable def LinearSys.closedForm (sys : LinearSys 𝕋 n) (x0 : Vec ℝ n) (u : ℝ → Vec ℝ n)
    (t : ℝ) : Vec ℝ n :=
  exp (t • toRealMat sys.A) *ᵥ x0 + ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
