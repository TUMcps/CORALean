module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrder
public import CORALean.ContDynamics.LinearSys.Operations.WithInputSplitReachStepk
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# Reachability with an input set anywhere, over `[tStart, tFinal]`

[1, Alg. 3]: the windows `τ_0, …, τ_{N-1}`, one `WithInputSplit.reachStepk`
each, collected as a `SetUnion`, `N = ⌈(tFinal - tStart) / Δt⌉` of them and never fewer
than one, exactly `LinearSys.WithInput.reach`'s count. No `box()` on the
accumulated input set, as there.

`X₀ = params.X₀`, `Δt = options.Δt`, `η = options.η`, the Taylor order
asked for, raised to `reachOrder Δt + 2` where that is higher: `timeIntervalStep`,
`inputSolution` and `constInputSolution` all hold only at an order admissible for `Δt` and
`sys.A`. The times are real, as in `LinearSys.reachWrappingFree`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈(tFinal - tStart) / Δt⌉` (at least one),
inputs in `sys.U` split at its centre, at order `η` raised until admissible. -/
noncomputable def LinearSys.WithInputSplit.reach (sys : LinearSys.WithInputSplit 𝕋 S n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachStepOptions ℝ) : SetUnion (S n) :=
  let X₀ := params.X₀                                           -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let N := max 1 ⌈(params.tFinal - params.tStart) / Δt⌉₊      -- windows τ_0, …, τ_{N-1}
  let η' := max η (sys.sys.reachOrder Δt + 2)                    -- η, raised until admissible
  ⟨(List.range N).map (sys.reachStepk Δt η' X₀)⟩                -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
