import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachCZ
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachInit
import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# `Alg. 2` lines 7-12: one iteration of the main loop

`maxBackReachStep`: [1, Alg. 2], propagating the two particular solutions and assembling
`R̂^{∃∀}(-τ_k)` from `P₁` and `P₂`. `ρ` is the caller's support oracle for a polytope — the
linear program of (9). `Zw` is (26), the constant centre trajectory's contribution over one
interval.

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

/-- Lines 7-12: one iteration of [1, Alg. 2]'s main loop, propagating the two
particular solutions and assembling `R̂^{∃∀}(-τ_k)` from `P₁` and `P₂`. -/
noncomputable def LinearSys.maxBackReachStep (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁ P₂ : HPolytope (Vec ℝ n)) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (Δt : ℝ) (η : ℕ)
    (s : LinearSys.MaxBackReachState n) : LinearSys.MaxBackReachState n :=
  let tk1 := s.t + Δt                                               -- 7. t_{k+1} ← t_k + Δt
  let Φk := exp (s.t • toRealMat sys.A)                             -- 7. e^{A t_k}
  let ZU := Zonotope.plus s.ZU (Zonotope.mtimes Φk                  -- 8. Z̲_U(t_{k+1})
    (Zonotope.mtimes (MatExp.expIntegral (toRealMat sys.A) Δt) U))
  let ZW₀ := Zonotope.plus s.ZW₀                                    -- 9. Ẑ_{W₀}(t_{k+1})
    (Zonotope.mtimes Φk (sys.inputSolution (S := 𝒵) Δt η W₀))
  let ZW := Zonotope.plus ZW₀ (Zw s.t)                              -- 10. Ẑ_W(τ_k)
  let CZ := ConZonotope.linComb                                     -- 11. conv(CZ(…), CZ(…))
    (LinearSys.maxBackReachCZ ρ P₁ ZW) (LinearSys.maxBackReachCZ ρ P₂ ZW)
  let R := ConZonotope.mtimes (exp ((-tk1) • toRealMat sys.A))  -- 12. e^{-A t_{k+1}}(CZ ⊕ -Z̲_U)
    (ConZonotope.plus CZ (Zonotope.conZonotope (Zonotope.mtimes (-(1 : Mat ℝ n n)) s.ZU)))
  { t := tk1, ZU := ZU, ZW₀ := ZW₀, ZW := ZW, R := R }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
