module

public import CORALean.ContDynamics.LinParamSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloat
public import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStepFloat
public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.ContDynamics.Reach.Operations.Steps
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# Reachability of a set-valued-matrix system in floats, window by window

`LinParamSys.reachUnion` computed in `𝕋`, homogeneous, as [1, Alg. 4] reads at a
constant parameter: the first window `H^R(τ_0)` by `timeIntervalStepFloat`,
reduced to order `ρ` as `LinearSys.reachWrappingFreeFloat` reduces it, and window
`k` by `reachStepkFloat`, `[e^{[A] t_k}]` applied to the first — never a power of
`[e^{[A]Δt}]`, so no window pays for the ones before it. `N = (tFinal - tStart) / Δt`
by `Reach.steps`; `η` raised by `reachOrderFloat`; `none` when either fails.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `τ_0, …, τ_{N-1}` of width `Δt` from `X₀` at every member of `sys.A`,
the first reduced to order `ρ`, at Taylor order `η` raised until admissible. -/
def LinParamSys.reachFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ) (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let HRτ₀ := Reduce.reduce (sys.timeIntervalStepFloat Δt η' X₀) ρ  -- H^R(τ_0), to order ρ
  (List.range N).mapM (sys.reachStepkFloat Δt η' HRτ₀)              -- H^R(τ_k), every k < N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
