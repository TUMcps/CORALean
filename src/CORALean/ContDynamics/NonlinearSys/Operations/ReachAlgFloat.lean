import CORALean.ContDynamics.NonlinearSys.Operations.LinReachRunFloat
import CORALean.ContDynamics.Reach.Operations.Steps

/-!
# Nonlinear reachability in floats: CORA's `nonlinearSys/reach` at `alg = 'lin'` or `'poly'`

`ẋ = f(x, u)`, `u(t) ∈ U` arbitrary in time, from `X₀`, computed in `𝕋` from a
`FloatHessModel` of `f`: `N = (tFinal - tStart) / Δt` steps of `linReachFloat`
(`linReachRunFloat`), each returning its set over the whole step. `N` is read as
`FloatModel.reachFloat` reads it, and `none` is returned where it is no natural number
or a step fails.

`NonlinearSys.polyReachRun` and `linReachPoly` are the real layer's `'poly'` loop and
step at supplied derivatives and certificates; this one computes its own from the
model, and its guarantee `reachAlgFloat_outer` is against the real system's runs
through `FloatHessModel.Encloses`, with no certificate and no confinement asked.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `R(τ_0), …, R(τ_{N-1})` of `ẋ = f(x, u)` from `X₀` under inputs in
`U`, each step abstracted by `alg`, [1, Alg. 1]'s `R([0, t_f])`. -/
def NonlinearSys.FloatHessModel.reachAlgFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (alg : NonlinearSys.LinReachAlg)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.R0                                               -- the paper's symbols
  let Δt := options.timeStep
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt)  -- (tFinal - tStart) / Δt ∈ ℕ
  fm.linReachRunFloat alg params.U options N X₀                     -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
