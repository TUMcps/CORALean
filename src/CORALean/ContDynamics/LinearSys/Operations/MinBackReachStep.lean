module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.MinBackReachInit
public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# `Alg. 1` lines 8-11: one iteration of the main loop

`minBackReachStep`: [1, Alg. 1], propagating the two particular solutions and the converted
target set over `τ_k`, over the time-inverted dynamics `ẋ̃ = -A x̃ - u - w`. `Zw` is (26), the
constant centre trajectory's contribution over one interval.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
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

/-- Lines 8-11: one iteration of [1, Alg. 1]'s main loop, propagating the two
particular solutions and the converted target set over `τ_k`. -/
noncomputable def LinearSys.minBackReachStep (sys : LinearSys 𝕋 n)
    (CZ : ConZonotope (Vec ℝ n)) (W₀ U₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (Δt : ℝ) (η : ℕ)
    (s : LinearSys.MinBackReachState n) : LinearSys.MinBackReachState n :=
  let Ā : LinearSys ℝ n := LinearSys.canonical (-toRealMat sys.A)  -- time-inverted dynamics
  let tk1 := s.t + Δt                                               -- 8. t_{k+1} ← t_k + Δt
  let Φk := exp (s.t • toRealMat Ā.A)                               -- 8. e^{-A t_k}
  let Φk1 := exp (tk1 • toRealMat Ā.A)                              -- 8. e^{-A t_{k+1}}
  let ZW₀ := Zonotope.plus s.ZW₀                                    -- 9. Ẑ_{W₀}(-t_{k+1})
    (Zonotope.mtimes Φk (Ā.inputSolution (S := 𝒵) Δt η W₀))
  let ZU₀ := Zonotope.plus s.ZU₀                                    -- 12. Ẑ_{U₀}(-t_{k+1})
    (Zonotope.mtimes Φk (Ā.inputSolution (S := 𝒵) Δt η U₀))
  let ZW := Zonotope.plus ZW₀ (Zw s.t)                              -- 10. Ẑ_W(-τ_k)
  let hull := ConZonotope.linComb (ConZonotope.mtimes Φk1 CZ)       -- 11. conv(…, …)
    (ConZonotope.mtimes Φk CZ)
  let curv := ConZonotope.mtimesIntervalMat                         -- 11. F e^{-A t_{k+1}} CZ
    (MatExp.correctionMatrix (toRealMat Ā.A) Δt η) (ConZonotope.mtimes Φk1 CZ)
  let R := ConZonotope.plus (ConZonotope.plus hull curv)            -- 11. ⊕ -Ẑ_W(-τ_k)
    (Zonotope.conZonotope (Zonotope.mtimes (-(1 : Mat ℝ n n)) ZW))
  { t := tk1, ZW₀ := ZW₀, ZU₀ := ZU₀, R := R }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
