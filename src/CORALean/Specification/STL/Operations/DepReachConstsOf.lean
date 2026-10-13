import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.Specification.STL.Definitions.DepReachConsts
import CORALean.Specification.STL.Operations.DepBloating
import CORALean.Specification.STL.Operations.DepCurvatureF
import CORALean.Specification.STL.Operations.DepCurvatureG
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.Plus

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

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 1 of [1, Alg. 1]. -/
noncomputable def STL.depReachConsts (A : Mat ℝ n n) (B : Mat ℝ n m) (U : Zonotope (Vec ℝ m))
    (Δt : ℝ) (κ : ℕ) : STL.DepReachConsts n :=
  let ũ := B *ᵥ U.c                                                -- ũ ← B c_u
  let U₀ := Zonotope.mtimes B (U.plus (Zonotope.ofPoint (-U.c)))     -- U₀ ← B(U ⊕ (-c_u))
  let T := MatExp.expIntegral A Δt                                  -- T ← (14)
  let F := STL.depCurvatureF A Δt κ                                 -- F ← (18)
  let G := STL.depCurvatureG A Δt κ                                 -- G ← (18)
  let D := STL.depBloating A U₀ Δt κ                                -- D ← (15)
  ⟨ũ, U₀, T, F, G, D⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
