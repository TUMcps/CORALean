import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
import CORALean.ContDynamics.LinParamSys.Operations.WithInputReachStepk
import CORALean.ContDynamics.LinearSys.Definitions.ReachParams
import CORALean.ContSet.SetUnion.SetUnion

/-!
# Reachability with inputs over `[0, tFinal]`, one window of width `Δt` at a time

[1, Alg. 4]'s loop, `0 ∈ U`: the windows `τ_0, …, τ_{N-1}`, one
`WithInput.reachStepk` each, collected as a `SetUnion`, `N = ⌈tFinal / Δt⌉` of
them and never fewer than one. No `box()` on the accumulated input set: that
bounds a zonotope's order and is a reduction, which an enclosure need not make.

`η` is the Taylor order asked for, raised to `reachOrder Δt + 2` where that is
higher: `timeIntervalStep` and `inputSolution` both hold only at an order
admissible for `Δt` and every member of `sys.A`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈p.tFinal / p.Δt⌉` (at least
one), inputs in `sys.U`, at order `p.η` raised until admissible. -/
noncomputable def LinParamSys.WithInput.reachUnion (sys : LinParamSys.WithInput S n)
    (p : LinearSys.ReachParams) (X₀ : S n) : SetUnion (S n) :=
  let N := max 1 ⌈p.tFinal / p.Δt⌉₊                             -- windows τ_0, …, τ_{N-1}
  let η' := max p.η (sys.sys.reachOrder p.Δt + 2)               -- η, raised until admissible
  ⟨(List.range N).map (sys.reachStepk p.Δt η' X₀)⟩              -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
