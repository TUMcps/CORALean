module

public import CORALean.ContDynamics.NonlinearSys.Operations.RelinRunFloat
public import CORALean.ContDynamics.Reach.Operations.Steps

@[expose] public section

/-!
# Nonlinear reachability in floats: CORA's `nonlinearSys/reach` at `alg = 'lin'`

`ẋ = f(x, u)`, `u(t) ∈ U` arbitrary in time, from `X₀`, computed in `𝕋` from a
`FloatModel` of `f`: `N = (tFinal - tStart) / Δt` re-linearized steps
(`relinRunFloat`), each returning its set over the whole step. `N` is read as
`LinearSys.reachFloatInput` reads it, through `Reach.steps`, and `none` is
returned where it is no natural number or a step fails.

`NonlinearSys.relinReach` and `WithSteps.reachUnion` are the real layer's same
loop, given the linearizations as certificates; this one computes its own, and its
guarantee `reachFloat_outer` is against the real system's runs through
`FloatModel.Encloses`, with no certificate and no confinement asked of anyone.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt)  -- (tFinal - tStart) / Δt ∈ ℕ
  fm.relinRunFloat params.U options N X₀                            -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
