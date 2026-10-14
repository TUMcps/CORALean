module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.Specification.STL.Definitions.DepReachConsts
public import CORALean.Specification.STL.Operations.DepBloating
public import CORALean.Specification.STL.Operations.DepCurvatureF
public import CORALean.Specification.STL.Operations.DepCurvatureG
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# Line 1 of the dependency preserving reachability algorithm

[1, Alg. 1], line 1: `ũ ← B c_u`, `U₀ ← B(U ⊕ (-c_u))`, `T ← (14)`, `F, G ← (18)`, `D ← (15)`.
`T` is `MatExp.expIntegral A Δt = ∫₀^{Δt} e^{Aσ} dσ`, which is `A⁻¹(e^{AΔt} - I)` for an invertible
`A` and the power series [1] integrates `A⁻¹` into otherwise.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 1 of [1, Alg. 1]. -/
noncomputable def STL.depReachConsts (A : Mat ℝ n n) (B : Mat ℝ n m) (U : Zonotope (Vec ℝ m))
    (Δt : ℝ) (κ : ℕ) : STL.DepReachConsts n :=
  -- 1. `ũ ← B c_u`
  let ũ := B *ᵥ U.c
  -- 1. `U₀ ← B(U ⊕ (-c_u))`
  let U₀ := Zonotope.mtimes B (U.plus (Zonotope.ofPoint (-U.c)))
  -- 1. `T ← (14)`
  let T := MatExp.expIntegral A Δt
  -- 1. `F ← (18)`
  let F := STL.depCurvatureF A Δt κ
  -- 1. `G ← (18)`
  let G := STL.depCurvatureG A Δt κ
  -- 1. `D ← (15)`
  let D := STL.depBloating A U₀ Δt κ
  ⟨ũ, U₀, T, F, G, D⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
