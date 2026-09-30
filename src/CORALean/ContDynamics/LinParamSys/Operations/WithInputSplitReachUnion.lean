import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
import CORALean.ContDynamics.LinParamSys.Operations.WithInputSplitReachStepk
import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
import CORALean.ContDynamics.Reach.Definitions.Params
import CORALean.ContSet.SetUnion.SetUnion

/-!
# Reachability with an input set anywhere, over `[tStart, tFinal]`

`LinParamSys.WithInput.reachUnion` with [1, Alg. 4]'s input set split: the
windows `τ_0, …, τ_{N-1}`, one `WithInputSplit.reachStepk` each, collected as a
`SetUnion`, `N = ⌈(tFinal - tStart) / Δt⌉` of them and never fewer than one.

`η = taylorTerms` is raised to `reachOrder Δt + 2` where that is higher, since only an
order admissible for `Δt` and every member of `sys.A` makes `timeIntervalStep`,
`constInputSolution` and `constPropagate` hold.

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
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈(tFinal - tStart) / Δt⌉` (at least
one), inputs in `sys.U` split at its centre, at order `taylorTerms` raised until
admissible. -/
noncomputable def LinParamSys.WithInputSplit.reachUnion (sys : LinParamSys.WithInputSplit S n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachStepOptions ℝ) : SetUnion (S n) :=
  let X₀ := params.R0                                             -- the paper's symbols
  let Δt := options.timeStep
  let N := max 1 ⌈(params.tFinal - params.tStart) / Δt⌉₊         -- windows τ_0, …, τ_{N-1}
  let η' := max options.taylorTerms (sys.sys.reachOrder Δt + 2)   -- η, raised until admissible
  ⟨(List.range N).map (sys.reachStepk Δt η' X₀)⟩                  -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
