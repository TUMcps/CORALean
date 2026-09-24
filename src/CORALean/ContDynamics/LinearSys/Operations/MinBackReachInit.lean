import CORALean.ContDynamics.LinearSys.Definitions.MinBackReachState
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

/-!
# `Alg. 1` lines 1-6: the loop state before the first iteration

`minBackReachInit`: [1, Alg. 1] lines 1-6, the two centred particular solutions
accumulated up to `t₀`, before the first iteration.

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

/-- Lines 1-6: the two centred particular solutions accumulated up to `t₀`,
before the first iteration. -/
noncomputable def LinearSys.minBackReachInit (sys : LinearSys 𝕋 n)
    (W₀ U₀ : Zonotope (Vec ℝ n)) (t₀ : ℝ) (η : ℕ) : LinearSys.MinBackReachState n :=
  let Ā : LinearSys ℝ n := ⟨-toRealMat sys.A⟩                       -- time-inverted dynamics
  { t := t₀                                                         -- 1. τ = [t₀, t_end]
    ZW₀ := Ā.inputSolution (S := 𝒵) t₀ η W₀                         -- 5. Ẑ_{W₀}(-t₀)
    ZU₀ := Ā.inputSolution (S := 𝒵) t₀ η U₀                         -- 6. Ẑ_{U₀}(-t₀)
    R := (Zonotope.ofPoint 0).conZonotope }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
