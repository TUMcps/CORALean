module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSys.Operations.ManualInitFloat
public import CORALean.ContDynamics.LinearSys.Operations.ManualRunFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.Reach.Operations.Steps
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# `Alg. 1` in floats: reachability at a fixed step, order and zonotope order

`ẋ = Ax + Bu`, `u(t) ∈ U` arbitrary in time, from `X₀` over `[tStart, tFinal]`, by
[1, Alg. 1] computed in `𝕋`: `N = (tFinal - tStart)/Δt` iterations from `manualInitFloat`,
returning `R̂(τ_0), …, R̂(τ_{N-1})`. `V = B U` is split at its stored centre, so `0 ∈ U` is
not asked. The order `η` is raised until the float enclosures admit it (`reachOrderFloat`),
as the other float reaches raise it; `Δt` must divide the horizon exactly.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the windows `R̂(τ_0), …, R̂(τ_{N-1})` of `ẋ = Ax + Bu` from `X₀` under
inputs in `U`, or `none`. -/
def LinearSys.manualReachFloat (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let V := Mtimes.mtimes (𝕄 := Mat 𝕋)  -- B U, in the state space
    (S := fun k => Zonotope (Vec 𝕋 k)) B params.U
  sys.manualRunFloat X₀ V Δt η' ρ N (LinearSys.manualInitFloat X₀)  -- 1.-11.

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
