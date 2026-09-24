import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
import CORALean.ContDynamics.LinParamSys.Operations.WithInputSplitReachStepk
import CORALean.ContDynamics.LinearSys.Definitions.ReachParams
import CORALean.ContSet.SetUnion.SetUnion

/-!
# Reachability with an input set anywhere, over `[0, p.tFinal]`

`LinParamSys.WithInput.reachUnion` with [1, Alg. 4]'s input set split: the
windows `τ_0, …, τ_{N-1}`, one `WithInputSplit.reachStepk` each, collected as a
`SetUnion`, `N = ⌈p.tFinal / p.Δt⌉` of them and never fewer than one.

`η` is raised to `reachOrder p.Δt + 2` where that is higher, since only an
order admissible for `Δt` and every member of `sys.A` makes `timeIntervalStep`,
`constInputSolution` and `constPropagate` hold.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
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

/-- One time-interval set per window `τ_k`, `k < ⌈p.tFinal / p.Δt⌉` (at least
one), inputs in `sys.U` split at its centre, at order `p.η` raised until
admissible. -/
noncomputable def LinParamSys.WithInputSplit.reachUnion (sys : LinParamSys.WithInputSplit S n)
    (p : LinearSys.ReachParams) (X₀ : S n) : SetUnion (S n) :=
  let N := max 1 ⌈p.tFinal / p.Δt⌉₊                              -- windows τ_0, …, τ_{N-1}
  let η' := max p.η (sys.sys.reachOrder p.Δt + 2)                 -- η, raised until admissible
  ⟨(List.range N).map (sys.reachStepk p.Δt η' X₀)⟩                -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
