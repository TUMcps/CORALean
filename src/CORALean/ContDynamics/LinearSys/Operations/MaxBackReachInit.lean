module

public import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachState
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# `Alg. 3` lines 1-2: the loop state before the first iteration

`maxBackReachInit`: [1, Alg. 3] lines 1-2, the two particular solutions accumulated up to
`t₀`, before the first iteration.

## Inputs
* `sys` – linear system
* `U` – input zonotope
* `W₀` – initial disturbance zonotope
* `t₀` – start time
* `η` – Taylor order

## Output
* loop state before the first iteration

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 1-2: the two particular solutions accumulated up to `t₀`, before the
first iteration. -/
noncomputable def LinearSys.maxBackReachInit (sys : LinearSys 𝕋 n)
    (U W₀ : Zonotope (Vec ℝ n)) (t₀ : ℝ) (η : ℕ) : LinearSys.MaxBackReachState n :=
  { t := t₀                                                         -- 1. τ = [t₀, t_end]
    ZU := Zonotope.mtimes                                           -- 2. Z̲_U(t₀), see (25)
      (MatExp.expIntegral (toRealMat sys.A) t₀) U
    ZW₀ := sys.inputSolution (S := 𝒵) t₀ η W₀                       -- 2. Ẑ_{W₀}(t₀), see (24)
    ZW := Zonotope.ofPoint 0
    R := (Zonotope.ofPoint 0).conZonotope }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
