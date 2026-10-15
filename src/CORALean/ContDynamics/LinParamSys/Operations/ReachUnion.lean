module

public import CORALean.ContDynamics.LinParamSys.Operations.InputSet
public import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkInput
public import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# Reachability with inputs over `[tStart, tFinal]`, one window of width `Δt` at a time

[1, Alg. 4]'s loop with CORA's `params.U`, in input coordinates, anywhere in the input space:
the windows `τ_0, …, τ_{N-1}`, one `reachStepkInput` each, collected as a `SetUnion`,
`N = ⌈(tFinal - tStart) / Δt⌉` of them and never fewer than one. The state-space input set
`V = B U ⊕ c` is formed here, as CORA's `priv_inputSolution` forms it, and each window splits
it at its center, so `0 ∈ U` is not asked: the remainder `V - ũ` holds the origin by
construction. No `box()` on the accumulated input set: that bounds a zonotope's order and is a
reduction, which an enclosure need not make.

`η = options.η` is the order asked for, raised to `reachOrder Δt + 2` where that is higher:
`timeIntervalStep`, `constInputSolution` and `inputSolution` hold only at an order admissible
for `Δt` and every member of `sys.A`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈(tFinal - tStart) / Δt⌉` (at least one),
under inputs `params.U` in input coordinates, at order `η` raised until admissible. -/
noncomputable def LinParamSys.reachUnion (sys : LinParamSys ℐ n)
    (params : Reach.InputParams (S n) (S sys.m) ℝ) (options : LinearSys.ReachStepOptions ℝ) :
    SetUnion (S n) :=
  let X₀ := params.X₀                                             -- the paper's symbols
  let Δt := options.Δt
  let N := max 1 ⌈(params.tFinal - params.tStart) / Δt⌉₊         -- windows τ_0, …, τ_{N-1}
  let η' := max options.η (sys.reachOrder Δt + 2)                 -- η, raised until admissible
  let V := sys.inputSet params.U                                  -- V = B U ⊕ c, in the state space
  ⟨(List.range N).map (sys.reachStepkInput Δt η' X₀ V)⟩           -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
