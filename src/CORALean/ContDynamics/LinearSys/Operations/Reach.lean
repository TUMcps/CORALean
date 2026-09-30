import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
import CORALean.ContDynamics.LinearSys.Operations.ReachStepk
import CORALean.ContDynamics.Reach.Definitions.Params
import CORALean.ContSet.SetUnion.SetUnion

/-!
# Reachability over `[tStart, tFinal]`, recursively, one window of width `Δt` at a time

`X₀ = params.R0`, `Δt = options.timeStep`, `η = options.taylorTerms`: the windows
`τ_0, …, τ_{N-1}`, one `reachStepk` each, collected as a `SetUnion`:
`N = ⌈(tFinal - tStart) / Δt⌉` of them, so the last may overshoot `tFinal`, which an outer
enclosure may. The times are real, unlike `Reach.steps`' rational ones: the ceiling is
part of what `reach_outer` says — a horizon that is no multiple of `Δt` is covered, where
`Reach.steps` would refuse it — and `ℝ` has no `ToRat`.

CORA's `standard` scheme, its default: [1, Alg. 4] at a point matrix, with no input and
no order reduction — `reachStepk`'s own recursion runs on the time-point sets `timePoint`,
and encloses window `τ_k` from `timePoint Δt X₀ k` alone.

Unlike `reachWrappingFree`, `η` is taken as given and `N` is not raised to one:
`reach_outer` asks for what `timeIntervalStep_outer` needs of the order, and for
`0 < tFinal`, instead.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


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
  let X₀ := params.R0                                           -- the paper's symbols
  let Δt := options.timeStep
  let η := options.taylorTerms
  let N := ⌈(params.tFinal - params.tStart) / Δt⌉₊              -- windows τ_0, …, τ_{N-1}
  ⟨(List.range N).map (sys.reachStepk Δt η X₀)⟩                -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
