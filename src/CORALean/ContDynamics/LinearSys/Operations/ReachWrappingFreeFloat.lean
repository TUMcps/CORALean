module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFreeFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalFloat
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.ContDynamics.Reach.Operations.Steps
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# Wrapping-free reachability in floats: `R(τ_k) = [e^{A t_k}] R(τ_0)`

[1, Alg. 1] without an input, computed in `𝕋`, CORA's `linAlg = 'wrapping-free'`, at `params` and
`options` read as `reachFloat` reads them: the first window is `timeIntervalFloat`, reduced by
Girard's rule to order `ρ`, and window `k < N` is that one set carried by an enclosure of
`e^{A t_k}` taken at `t_k` directly (`reachStepkWrappingFreeFloat`), so no window's error
compounds into the next one's. `η` is raised with `reachOrderFloat` to the first order from
`max η 2` the float remainder bound at `Δt · A` admits; each window scales `t_k` down to the step
by squarings and keeps that order. `N = (tFinal - tStart) / Δt` by `Reach.steps`; `none` when
that is no natural number or a search fails.

## Inputs
* `sys` – linear system
* `params` – reach parameters
* `options` – reach options

## Output
* float windows of the run, if it completes

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `τ_0, …, τ_{N-1}` of width `Δt` from `X₀`, the first reduced to
order `ρ`, at Taylor order `η` raised until admissible. -/
def LinearSys.reachWrappingFreeFloat (sys : LinearSys 𝕋 n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ) (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let Rτ₀ := Reduce.reduce (sys.timeIntervalFloat Δt η' X₀) ρ   -- R(τ_0), to order ρ
  (List.range N).mapM (sys.reachStepkWrappingFreeFloat Δt η' Rτ₀)     -- R(τ_k) = [e^{A t_k}] R(τ_0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
