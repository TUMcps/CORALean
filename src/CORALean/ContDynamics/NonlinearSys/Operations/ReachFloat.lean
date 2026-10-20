module

public import CORALean.ContDynamics.NonlinearSys.Operations.RelinRunFloat
public import CORALean.ContDynamics.Reach.Operations.Steps

@[expose] public section

/-!
# Nonlinear reachability in floats: CORA's `nonlinearSys/reach` at `alg = 'lin'`

`ẋ = f(x, u)`, `u(t) ∈ U` arbitrary in time, from `X₀`, computed in `𝕋` from a `FloatModel` of
`f`: `N = (tFinal - tStart) / Δt` re-linearized steps (`relinRunFloat`), each returning its set
over the whole step. `N` is read as `LinearSys.reachFloatInput` reads it, through `Reach.steps`,
and `none` is returned where it is no natural number or a step fails. The real layer's same loop
is `NonlinearSys.relinReach`, given certificates; this one computes its own, and its guarantee
`reachFloat_outer` is against the real system's runs through `FloatModel.Encloses`.

## Inputs
* `fm` – float model
* `params` – reachability parameters
* `options` – reachability options

## Output
* the time-interval sets of all steps, or none

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `R(τ_0), …, R(τ_{N-1})` of `ẋ = f(x, u)` from `X₀` under inputs in
`U`, re-linearizing once per step, [1, Alg. 1]'s `R([0, t_f])`. -/
def NonlinearSys.FloatModel.reachFloat (fm : NonlinearSys.FloatModel 𝕋 n m)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  -- 2. the loop runs while `t_k < t_end`: `N = (tFinal - tStart) / Δt` iterations
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt)  -- (tFinal - tStart) / Δt ∈ ℕ
  -- 3.-17. the iterations; 18. their `R(τ_k)`, `⋃_{k < N} R(τ_k)`
  fm.relinRunFloat params.U options N X₀                            -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
