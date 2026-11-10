module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval
public import CORALean.ContDynamics.LinearSys.Operations.TimePoint
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# Reachability over `[tStart, tFinal]`, recursively, one window of width `Δt` at a time

`X₀ = params.X₀`, `Δt = options.Δt`, `η = options.η`: the windows `τ_0, …, τ_{N-1}`, one
`timeInterval` each, collected as a `SetUnion`: `N = ⌈(tFinal - tStart) / Δt⌉` of them, so the last
may overshoot `tFinal`, which an outer enclosure may. The times are real, unlike `Reach.steps`'
rational ones: the ceiling is part of what `reach_outer` says, a horizon that is no multiple of
`Δt` is covered, where `Reach.steps` would refuse it, and `ℝ` has no `ToRat`. CORA's `standard`
scheme, its default: [1, Alg. 1] at a point matrix, with no input and no order reduction; each
time-point set `timePoint` is computed once and handed to `timeInterval` at both ends of its
window. Unlike `reachWrappingFree`, `η` is taken as given and `N` is not raised to one.

## Inputs
* `sys` – linear system
* `params` – reach parameters
* `options` – step options

## Output
* time-interval sets of the windows

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {ContSet : ℕ → Type} [∀ n, ContSetLike (ContSet n) (Vec ℝ n)]
variable [∀ n, Plus (ContSet n) (Vec ℝ n)] [∀ n, LinComb (ContSet n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) ContSet] [Mtimes ℐ ContSet]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈(tFinal - tStart) / Δt⌉`, at order `η`. -/
noncomputable def LinearSys.reach (sys : LinearSys 𝕋 n) (params : Reach.Params (ContSet n) ℝ)
    (options : LinearSys.ReachOptions ℝ) : SetUnion (ContSet n) :=
  let X₀ := params.X₀                                           -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let N := ⌈(params.tFinal - params.tStart) / Δt⌉₊              -- windows τ_0, …, τ_{N-1}
  let X := sys.timePoint Δt X₀                                  -- R(t_k), each once
  ⟨(List.range N).map fun k => sys.timeInterval Δt η (X k) (X (k + 1))⟩  -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
