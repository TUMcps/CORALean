import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
import CORALean.ContDynamics.LinParamSys.Operations.WithInputReachStepk
import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
import CORALean.ContDynamics.Reach.Definitions.Params
import CORALean.ContSet.SetUnion.SetUnion

/-!
# Reachability with inputs over `[tStart, tFinal]`, one window of width `Δt` at a time

[1, Alg. 4]'s loop, `0 ∈ U`: the windows `τ_0, …, τ_{N-1}`, one
`WithInput.reachStepk` each, collected as a `SetUnion`, `N = ⌈(tFinal - tStart) / Δt⌉`
of them and never fewer than one. No `box()` on the accumulated input set: that
bounds a zonotope's order and is a reduction, which an enclosure need not make.

`η = taylorTerms` is the order asked for, raised to `reachOrder Δt + 2` where that is
higher: `timeIntervalStep` and `inputSolution` both hold only at an order
admissible for `Δt` and every member of `sys.A`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈(tFinal - tStart) / Δt⌉` (at least
one), inputs in `sys.U`, at order `taylorTerms` raised until admissible. -/
noncomputable def LinParamSys.WithInput.reachUnion (sys : LinParamSys.WithInput S n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachStepOptions ℝ) : SetUnion (S n) :=
  let X₀ := params.R0                                             -- the paper's symbols
  let Δt := options.timeStep
  let N := max 1 ⌈(params.tFinal - params.tStart) / Δt⌉₊         -- windows τ_0, …, τ_{N-1}
  let η' := max options.taylorTerms (sys.sys.reachOrder Δt + 2)   -- η, raised until admissible
  ⟨(List.range N).map (sys.reachStepk Δt η' X₀)⟩                  -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
