import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
import CORALean.ContDynamics.LinearSys.Operations.ReachOrder
import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFree
import CORALean.ContDynamics.Reach.Definitions.Params
import CORALean.ContSet.SetUnion.SetUnion

/-!
# Reachability over `[tStart, tFinal]`, one window of width `Δt` at a time

`X₀ = params.X₀`, `Δt = options.Δt`, `η = options.η`. The windows
`τ_0, …, τ_{N-1}`, one `reachStepkWrappingFree` each, collected as a `SetUnion`:
`N = ⌈(tFinal - tStart) / Δt⌉` of them, so the last may overshoot `tFinal`, which an outer
enclosure may, and never fewer than one, so `tFinal = tStart` still keeps `X₀`. The times
are real: the ceiling is part of what `reachWrappingFree_outer` says, a horizon that is no
multiple of `Δt` covered, and `ℝ` has no `ToRat` for `Reach.steps`.

`η` is the Taylor order asked for, raised to `reachOrder Δt + 2` where that is
higher: `timeIntervalStep_outer` holds only at an order admissible for `Δt` and
`sys.A`, and this is where the matrix is at hand to decide it, so `reachWrappingFree_outer`
asks for no side condition on `η` at all.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈(tFinal - tStart) / Δt⌉` (at least one),
at order `η` raised until admissible. -/
noncomputable def LinearSys.reachWrappingFree (sys : LinearSys 𝕋 n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachStepOptions ℝ) : SetUnion (S n) :=
  let X₀ := params.X₀                                           -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let N := max 1 ⌈(params.tFinal - params.tStart) / Δt⌉₊      -- windows τ_0, …, τ_{N-1}
  let η' := max η (sys.reachOrder Δt + 2)                        -- η, raised until admissible
  ⟨(List.range N).map (sys.reachStepkWrappingFree Δt η' X₀)⟩    -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
