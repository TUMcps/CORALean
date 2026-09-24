import CORALean.ContDynamics.LinearSys.Operations.ReachOrder
import CORALean.ContDynamics.LinearSys.Operations.WithInputReachStepk
import CORALean.ContSet.SetUnion.SetUnion

/-!
# Reachability with inputs over `[0, tFinal]`, one window of width `Δt` at a time

[1, Alg. 2], `0 ∈ U`: the windows `τ_0, …, τ_{N-1}`, one `reachStepk` each,
collected as a `SetUnion`, `N = ⌈tFinal / Δt⌉` of them and never fewer than one,
exactly `LinearSys.reach`'s count. No `box()` on the accumulated input set: that
bounds a zonotope's order and is a reduction, which an enclosure need not make.

`η` is the Taylor order asked for, raised to `reachOrder Δt + 2` where that is
higher, as in `LinearSys.reach`: `timeIntervalStep_outer` and `inputSolution`'s
enclosure both hold only at an order admissible for `Δt` and `sys.A`.

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

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈tFinal / Δt⌉` (at least one),
inputs in `sys.U`, at order `η` raised until admissible. -/
noncomputable def LinearSys.WithInput.reach (sys : LinearSys.WithInput 𝕋 S n)
    (tFinal Δt : ℝ) (η : ℕ) (X₀ : S n) : SetUnion (S n) :=
  let N := max 1 ⌈tFinal / Δt⌉₊                                 -- windows τ_0, …, τ_{N-1}
  let η' := max η (sys.sys.reachOrder Δt + 2)                    -- η, raised until admissible
  ⟨(List.range N).map (sys.reachStepk Δt η' X₀)⟩                -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
