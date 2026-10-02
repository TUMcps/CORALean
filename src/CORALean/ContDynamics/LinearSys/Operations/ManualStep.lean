import CORALean.ContDynamics.LinearSys.Definitions.ManualState
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosure
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# `Alg. 1` lines 5-11: one iteration of the main loop

`manualStep`: [1, Alg. 1], a fixed time step `Δt`, truncation order `η` and zonotope order
`ρ`, no search anywhere.

`P^u`, the exact particular solution due to the constant part `ũ` of the input, is a
`Vec ℝ n` rather than a set: [1]'s own `⊕` at lines 6 and 25 is plain vector addition there,
`P^u` never being reduced or widened. `C`, line 8's curvature enclosure, and the `η,ρ`-free
`ũ, U₀` split of line 1, are exactly `MatExp.curvatureEnclosure` and the derivation this file
repeats every step rather than threading through the state, since both are pure functions of
`U`, `Δt`, `η` alone.

One correction to the printed algorithm. Line 5 assigns `τ_{k+1} ← [t_k,t_{k+1}]`, but every
later line (9, 11, 13) reads `τ_k`, which line 5 never sets — an index one step out of the
kind this project has found before (see the reference page's `Alg. 1` finding). `manualStep`
computes the interval Line 9 obviously means, `[t_k,t_{k+1}]`, under the name the rest of the
algorithm uses for it.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
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

/-- Lines 5-11: one iteration of [1, Alg. 1]'s main loop, and `R̂(τ_k)`. -/
noncomputable def LinearSys.manualStep (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n))
    (Δt : ℝ) (η ρ : ℕ) (s : LinearSys.ManualState n) :
    LinearSys.ManualState n × Zonotope (Vec ℝ n) :=
  let ũ := U.c                                                          -- 1. ũ ← Bc_u + p
  let U₀ : Zonotope (Vec ℝ n) := { h := U.h, c := 0, G := U.G }          -- 1. U₀ ← ⟨0,BG_u⟩_Z
  let PuΔt := sys.stepInputConst ũ Δt                                   -- 3. P^u(Δt), eq. (19)
  let PUΔt := sys.inputSolution (S := 𝒵) Δt η U₀                        -- 3. P̂^U(Δt), eq. (20)
  let tk1 := s.t + Δt                                                   -- 5. t_{k+1}
  let Φtk := exp (s.t • toRealMat sys.A)                                -- 6. e^{A t_k}
  let Puk1 := s.Pu + Φtk *ᵥ PuΔt                                        -- 6. P^u(t_{k+1})
  let Φtk1 := exp (tk1 • toRealMat sys.A)                               -- 7. e^{A t_{k+1}}
  let Hk1 := Zonotope.plus (Zonotope.mtimes Φtk1 X₀) (Zonotope.ofPoint Puk1)  -- 7. H(t_{k+1})
  let C := MatExp.curvatureEnclosure (toRealMat sys.A) s.H ũ Δt η        -- 8. C, eq. (15)-(16)
  let Hτk := Zonotope.plus (Zonotope.linComb s.H Hk1) C                  -- 9. Ĥ(τ_k)
  let PUsum := Zonotope.plus s.PU (Zonotope.mtimes Φtk PUΔt)             -- 10. inside `reduce(·,ρ)`
  let PUk1 := Zonotope.reduce PUsum ρ                                    -- 10. P̂^U(t_{k+1})
  let Rτk := Zonotope.plus Hτk PUk1                                      -- 11. R̂(τ_k)
  ({ t := tk1, H := Hk1, Pu := Puk1, PU := PUk1 }, Rτk)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
