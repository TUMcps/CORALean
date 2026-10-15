module

public import CORALean.ContDynamics.LinParamSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.LinParamSys.Theorems.WithInputReachUnionOuter
public import CORALean.ContDynamics.LinParamSys.Theorems.WithInputSplitReachUnionOuter
public import CORALean.ContDynamics.Interfaces

@[expose] public section

/-!
# `LinParamSys` instantiates `ContDynamics`, and with its input wrappers `Reach`

`params` is `Reach.Params` at real time, `options` `LinearSys.ReachStepOptions`, the
point case's. `reachExact` is `reachUnionExact` on `[0, tFinal - tStart]`, the system
being time-invariant, `reach` is `reachUnion`, `none` unless `0 < Δt`, and the
guarantee is `reachUnion_outer`, for each — constant-parameter, in
`⌈(tFinal - tStart) / Δt⌉` windows. `LinParamSys ℐ` is homogeneous;
`LinParamSys.WithInput` carries the input set, `0 ∈ U` among its fields, so `U` is the
system's rather than `params`', and asks the representation to be convex and compact,
what `inputSolution`'s enclosure needs of `U`; `LinParamSys.WithInputSplit` drops
`0 ∈ U` and asks for `Recentre` too — [1, Alg. 4]'s split case.

`LinParamSys` is a `ContDynamics`: `m` inputs and no disturbance, a run a `Trajectory` —
`'varParam'`, a fresh `A t` and `B t` at every instant, which every `'constParam'` run is too —
at some such matrices.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance LinParamSys.reachInstance :
    Reach (LinParamSys ℐ) (fun n => Reach.Params (S n) ℝ) (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reachUnion params options) else none
  reach_outer sys params options _ hR := by
    -- `none` is equal to no `some R`, so only the run the side conditions admit is left
    split_ifs at hR with h
    cases hR
    exact sys.reachUnion_outer params h

noncomputable instance LinParamSys.WithInput.reachInstance
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinParamSys.WithInput S) (fun n => Reach.Params (S n) ℝ)
      (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reachUnion params options) else none
  reach_outer sys params options _ hR := by
    -- `none` is equal to no `some R`, so only the run the side conditions admit is left
    split_ifs at hR with h
    cases hR
    exact sys.reachUnion_outer params h

noncomputable instance LinParamSys.WithInputSplit.reachInstance
    [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinParamSys.WithInputSplit S) (fun n => Reach.Params (S n) ℝ)
      (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reachUnion params options) else none
  reach_outer sys params options _ hR := by
    -- `none` is equal to no `some R`, so only the run the side conditions admit is left
    split_ifs at hR with h
    cases hR
    exact sys.reachUnion_outer params h

/-- CORA's `linParamSys` as a `ContDynamics`, its runs the time-varying-parameter ones. -/
instance LinParamSys.contDynamics {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
    {n : ℕ} : ContDynamics (LinParamSys 𝕄 n) n where
  nrOfInputs sys := sys.m
  nrOfDisturbances _ := 0
  Trajectory sys T X₀ U W x u w :=
    (∃ A B, LinParamSys.Trajectory (S := 𝒮) sys T X₀ U x u A B) ∧
      ∀ t ∈ T, w t ∈ W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
