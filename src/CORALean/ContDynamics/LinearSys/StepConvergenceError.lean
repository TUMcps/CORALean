import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

/-!
# The two halves of a step's error that converge and decrease superlinearly

[1]: `ε_H` and `ε_P` (eq. 21-22) are the enclosing radius of the *widening*
term alone — `Fx(Δt,η)X₀ ⊕ Fu(Δt,η)c_u` at the homogeneous solution,
`E(Δt,η)·Δt·U` at the particular one — not `timeIntervalStepError` /
`timePointStepError`'s combined figure, which also carries a *hull* term
(independent of `η`, first order in the step) that [1] does not fold into
either quantity. Both names here are exactly those two functions' non-hull
halves, scaled by the same `∑ⱼ absBound j` every radius in this file already
scales by, and at the base step `[0,r]` — the pre-multiplication by `e^{At_i}`
that turns a base step into the `i`-th one is composition, out of scope here as
it is for `StepError` itself.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ε_H`'s widening term alone (eq. 21) — the correction matrix's own
radius, `timeIntervalStepError` without its hull term. -/
noncomputable def LinearSys.timeIntervalStepCurvatureError (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (X₀ : Zonotope (Vec ℝ n)) : ℝ :=
  2 * (∑ j, X₀.absBound j) * (Real.exp (r * ‖toRealMat sys.A‖) - 1 - r * ‖toRealMat sys.A‖
    + MatExp.expRemainderBound (r • toRealMat sys.A) η)

/-- `ε_P`'s widening term alone (eq. 22) — `timePointStepError` without
its dependency term. -/
noncomputable def LinearSys.timePointStepRemainderError (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (U : Zonotope (Vec ℝ n)) : ℝ :=
  2 * (∑ j, U.absBound j) * (r * MatExp.expRemainderBound (r • toRealMat sys.A) η)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
