module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveIntegralFloat
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.Specification.STL.Definitions.DepReachConstsFloat
public import CORALean.Specification.STL.Operations.DepBloatingFloat
public import CORALean.Specification.STL.Operations.DepCurvatureFFloat
public import CORALean.Specification.STL.Operations.DepCurvatureGFloat
public import CORALean.Specification.STL.Operations.DepReachConstsOf

@[expose] public section

/-!
# Line 1 of the dependency preserving reachability algorithm, over floats

[1, Alg. 1], line 1: `ũ ← B c_u`, `U₀ ← B(U ⊕ (-c_u))`, `T ← (14)`, `F, G ← (18)`, `D ← (15)` with
the bounds held in `𝕋`. `T` is `∫₀^{Δt} e^{Aσ} dσ` as the float interval matrix
`MatExp.adaptiveIntegral` of the point box `A`, the orders up to `κ` summed and the tail in the
float remainder; `ũ` is the point `B c_u` and `U₀` the product with `U ⊕ (-c_u)`, each with its
rounding in the error box. Soundness is `STL.depReachConstsFloat_outer`.
## Inputs
* `A` – float dynamics matrix
* `B` – float input matrix
* `U` – float input zonotope
* `Δt` – float time step
* `κ` – Taylor order

## Output
* the constants computed in the first line
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 1 of [1, Alg. 1], rounded outward. -/
def STL.depReachConstsFloat (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (U : Float.Zonotope (Vec 𝕋 m))
    (Δt : 𝕋) (κ : ℕ) : STL.DepReachConstsFloat 𝕋 n :=
  -- 1. `ũ ← B c_u`
  let ũ := Zonotope.mtimes B (Zonotope.point U.c)
  -- 1. `U₀ ← B(U ⊕ (-c_u))`
  let U₀ := Zonotope.mtimes B (U.plus (Zonotope.point (-U.c)))
  -- 1. `T ← (14)`
  let T := MatExp.adaptiveIntegral (Interval.point A) Δt κ
  -- 1. `F ← (18)`
  let F := STL.depCurvatureFFloat A Δt κ
  -- 1. `G ← (18)`
  let G := STL.depCurvatureGFloat A Δt κ
  -- 1. `D ← (15)`
  let D := STL.depBloatingFloat A U₀ Δt κ
  ⟨ũ, U₀, T, F, G, D⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
