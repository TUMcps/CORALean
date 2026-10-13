module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

@[expose] public section

/-!
# `ε_H`'s widening term alone

[1]: `ε_H` (eq. 21) is the enclosing radius of the *widening* term alone —
`Fx(Δt,η)X₀ ⊕ Fu(Δt,η)c_u` at the homogeneous solution — not
`timeIntervalStepError`'s combined figure, which also carries a *hull* term
(independent of `η`, first order in the step) that [1] does not fold into it.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
