module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
public import CORALean.ContDynamics.LinearSys.Operations.ReachStepk
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# Reachability over `[tStart, tFinal]`, recursively, one window of width `Δt` at a time

`X₀ = params.X₀`, `Δt = options.Δt`, `η = options.η`: the windows `τ_0, …, τ_{N-1}`, one
`reachStepk` each, collected as a `SetUnion`: `N = ⌈(tFinal - tStart) / Δt⌉` of them, so the last
may overshoot `tFinal`, which an outer enclosure may. The times are real, unlike `Reach.steps`'
rational ones: the ceiling is part of what `reach_outer` says, a horizon that is no multiple of
`Δt` is covered, where `Reach.steps` would refuse it, and `ℝ` has no `ToRat`. CORA's `standard`
scheme, its default: [1, Alg. 1] at a point matrix, with no input and no order reduction;
`reachStepk`'s recursion runs on the time-point sets `timePoint`. Unlike `reachWrappingFree`,
`η` is taken as given and `N` is not raised to one.

## Inputs
* `sys` – linear system
* `params` – reach parameters
* `options` – step options

## Output
* time-interval sets of the windows

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈(tFinal - tStart) / Δt⌉`, at order `η`. -/
noncomputable def LinearSys.reach (sys : LinearSys 𝕋 n) (params : Reach.Params (S n) ℝ)
    (options : LinearSys.ReachStepOptions ℝ) : SetUnion (S n) :=
  let X₀ := params.X₀                                           -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let N := ⌈(params.tFinal - params.tStart) / Δt⌉₊              -- windows τ_0, …, τ_{N-1}
  ⟨(List.range N).map (sys.reachStepk Δt η X₀)⟩                -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
