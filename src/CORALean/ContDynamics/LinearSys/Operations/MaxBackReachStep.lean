module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachCZ
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachInit
public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ConZonotope

@[expose] public section

/-!
# `Alg. 3` lines 7-12: one iteration of the main loop

`maxBackReachStep`: [1, Alg. 3], propagating the two particular solutions and assembling
`R̂^{∃∀}(-τ_k)` from `P₁` and `P₂`. `ρ` is the caller's support oracle for a bounded polytope —
the linear program of (9); the inequality rows of `P₁`, `P₂` bound them, so their erosions are
bounded too. `Zw` is (27), the constant center trajectory's contribution over one interval.

## Inputs
* `sys` – linear system
* `ρ` – support oracle for bounded polytopes
* `P₁` – first eroded polytope
* `P₂` – second eroded polytope
* `U` – input zonotope
* `W₀` – initial disturbance zonotope
* `Zw` – center trajectory contribution
* `Δt` – step length
* `η` – Taylor order
* `s` – loop state

## Hypotheses
* `hP₁` – the inequality rows of `P₁` bound it
* `hP₂` – the inequality rows of `P₂` bound it

## Output
* next loop state with the step's backward reachable set
## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       19-September-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 7-12: one iteration of [1, Alg. 3]'s main loop, propagating the two
particular solutions and assembling `R̂^{∃∀}(-τ_k)` from `P₁` and `P₂`. -/
noncomputable def LinearSys.maxBackReachStep (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (_ : Bornology.IsBounded P.construct)
      (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (P₁ P₂ : HPolytope (Vec ℝ n)) (hP₁ : Bornology.IsBounded P₁.dropEqs.construct)
    (hP₂ : Bornology.IsBounded P₂.dropEqs.construct) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (Δt : ℝ) (η : ℕ)
    (s : LinearSys.MaxBackReachState n) : LinearSys.MaxBackReachState n :=
  -- 7. t_{k+1} ← t_k + Δt
  let tk1 := s.t + Δt
  -- 7. e^{A t_k}
  let Φk := exp (s.t • toRealMat sys.A)
  -- 8. Z̲_U(t_{k+1})
  let ZU := Zonotope.plus s.ZU (Zonotope.mtimes Φk
    (Zonotope.mtimes (MatExp.expIntegral (toRealMat sys.A) Δt) U))
  -- 9. Ẑ_{W₀}(t_{k+1})
  let ZW₀ := Zonotope.plus s.ZW₀
    (Zonotope.mtimes Φk (sys.inputSolution (S := 𝒵) Δt η W₀))
  -- 10. Ẑ_W(τ_k)
  let ZW := Zonotope.plus ZW₀ (Zw s.t)
  -- 11. conv(CZ(…), CZ(…))
  let CZ := ConZonotope.linComb
    (LinearSys.maxBackReachCZ ρ P₁ hP₁ ZW) (LinearSys.maxBackReachCZ ρ P₂ hP₂ ZW)
  -- 12. e^{-A t_{k+1}}(CZ ⊕ -Z̲_U)
  let R := ConZonotope.mtimes (exp ((-tk1) • toRealMat sys.A))
    (ConZonotope.plus CZ (Zonotope.conZonotope (Zonotope.mtimes (-(1 : Mat ℝ n n)) s.ZU)))
  { t := tk1, ZU := ZU, ZW₀ := ZW₀, ZW := ZW, R := R }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
