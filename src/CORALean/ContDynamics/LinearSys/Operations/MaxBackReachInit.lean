import CORALean.ContDynamics.LinearSys.Definitions.MaxBackReachState
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

/-!
# `Alg. 2` lines 1-2: the loop state before the first iteration

`maxBackReachInit`: [1, Alg. 2] lines 1-2, the two particular solutions accumulated up to
`t₀`, before the first iteration.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


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
    ZU := Zonotope.mtimes                                           -- 2. Z̲_U(t₀), see (24)
      (MatExp.expIntegral (toRealMat sys.A) t₀) U
    ZW₀ := sys.inputSolution (S := 𝒵) t₀ η W₀                       -- 2. Ẑ_{W₀}(t₀), see (23)
    ZW := Zonotope.ofPoint 0
    R := (Zonotope.ofPoint 0).conZonotope }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
