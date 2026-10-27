module

public import CORALean.ContDynamics.LinearSys.Definitions.ManualState
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosure
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# `Alg. 1` lines 5-11: one iteration of the main loop

`manualStep`: [1, Alg. 1], a fixed time step `Δt`, truncation order `η` and zonotope order `ρ`, no
search anywhere. `P^u`, the exact particular solution due to the constant part `ũ` of the input,
is a `Vec ℝ n` rather than a set: [1]'s own `⊕` at lines 6 and 25 is plain vector addition there.
`C`, line 8's curvature enclosure, and the `ũ, U₀` split of line 1 are `MatExp.curvatureEnclosure`
and a derivation this file repeats every step, both pure functions of `U`, `Δt`, `η`. One
correction to the printed algorithm: line 5 assigns `τ_{k+1} ← [t_k,t_{k+1}]`, but every later
line (9, 11, 13) reads `τ_k`, which line 5 never sets (see the reference page's `Alg. 1` finding).
`manualStep` computes the interval line 9 means, `[t_k,t_{k+1}]`, under the name the rest uses.

## Inputs
* `sys` – linear system
* `X₀` – initial zonotope
* `U` – input zonotope
* `Δt` – step length
* `η` – Taylor order
* `ρ` – zonotope order
* `s` – loop state

## Output
* next loop state and time-interval set

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 5-11: one iteration of [1, Alg. 1]'s main loop, and `R̂(τ_k)`. -/
noncomputable def LinearSys.manualStep (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n))
    (Δt : ℝ) (η ρ : ℕ) (s : LinearSys.ManualState n) :
    LinearSys.ManualState n × Zonotope (Vec ℝ n) :=
  -- 1. ũ ← Bc_u + p
  let ũ := U.c
  -- 1. U₀ ← ⟨0,BG_u⟩_Z
  let U₀ : Zonotope (Vec ℝ n) := { h := U.h, c := 0, G := U.G }
  -- 3. P^u(Δt), eq. (19)
  let PuΔt := sys.stepInputConst ũ Δt
  -- 3. P̂^U(Δt), eq. (20)
  let PUΔt := sys.inputSolution (S := 𝒵) Δt η U₀
  -- 5. t_{k+1}
  let tk1 := s.t + Δt
  -- 6. e^{A t_k}
  let Φtk := exp (s.t • toRealMat sys.A)
  -- 6. P^u(t_{k+1})
  let Puk1 := s.Pu + Φtk *ᵥ PuΔt
  -- 7. e^{A t_{k+1}}
  let Φtk1 := exp (tk1 • toRealMat sys.A)
  -- 7. H(t_{k+1})
  let Hk1 := Zonotope.plus (Zonotope.mtimes Φtk1 X₀) (Zonotope.ofPoint Puk1)
  -- 8. C, eq. (15)-(16)
  let C := MatExp.curvatureEnclosure (toRealMat sys.A) s.H ũ Δt η
  -- 9. Ĥ(τ_k)
  let Hτk := Zonotope.plus (Zonotope.linComb s.H Hk1) C
  -- 10. inside `reduce(·,ρ)`
  let PUsum := Zonotope.plus s.PU (Zonotope.mtimes Φtk PUΔt)
  -- 10. P̂^U(t_{k+1})
  let PUk1 := Zonotope.reduce PUsum ρ
  -- 11. R̂(τ_k)
  let Rτk := Zonotope.plus Hτk PUk1
  ({ t := tk1, H := Hk1, Pu := Puk1, PU := PUk1 }, Rτk)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
