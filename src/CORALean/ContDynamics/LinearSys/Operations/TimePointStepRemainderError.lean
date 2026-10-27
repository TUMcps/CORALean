module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

@[expose] public section

/-!
# `ε_P`'s widening term alone

[1]: `ε_P` (eq. 22) is the enclosing radius of the *widening* term alone —
`E(Δt,η)·Δt·U` at the particular solution — not `timePointStepError`'s
combined figure.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `U` – input zonotope

## Output
* radius of the remainder widening term

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
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

/-- `ε_P`'s widening term alone (eq. 22) — `timePointStepError` without
its dependency term. -/
noncomputable def LinearSys.timePointStepRemainderError (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (U : Zonotope (Vec ℝ n)) : ℝ :=
  2 * (∑ j, U.absBound j) * (r * MatExp.expRemainderBound (r • toRealMat sys.A) η)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
