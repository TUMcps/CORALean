import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
import CORALean.ContDynamics.LinParamSys.Operations.ReachStepk
import CORALean.ContDynamics.LinearSys.Definitions.ReachParams
import CORALean.ContSet.SetUnion.SetUnion

/-!
# The homogeneous flow over `[0, tFinal]`, one window of width `Δt` at a time

[1, Alg. 4]'s loop at `U = {0}`: the windows `τ_0, …, τ_{N-1}`, one
`reachStepk` each, collected as `Reach`'s `SetUnion`, `N = ⌈tFinal / Δt⌉` of
them and never fewer than one, exactly `LinearSys.reachWrappingFree`'s count. `η` is the
Taylor order asked for, raised to `reachOrder Δt + 2` where that is higher:
`timeIntervalStep`'s enclosure holds only at an order admissible for `Δt`.

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
open Matrix ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One homogeneous set per window `τ_k`, `k < ⌈p.tFinal / p.Δt⌉` (at least
one), at every member of `sys.A`, at order `p.η` raised until admissible. -/
noncomputable def LinParamSys.reachUnion (sys : LinParamSys ℐ n) (p : LinearSys.ReachParams)
    (X₀ : S n) : SetUnion (S n) :=
  let N := max 1 ⌈p.tFinal / p.Δt⌉₊                             -- windows τ_0, …, τ_{N-1}
  let η' := max p.η (sys.reachOrder p.Δt + 2)                   -- η, raised until admissible
  ⟨(List.range N).map (sys.reachStepk p.Δt η' X₀)⟩              -- ⋃_{k < N} H^R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
