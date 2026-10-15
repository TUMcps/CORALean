module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachAdmissibleOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ReachWrappingFreeOuter
public import CORALean.ContDynamics.LinearSys.Theorems.WithInputReachOuter
public import CORALean.ContDynamics.LinearSys.Theorems.WithInputSplitReachOuter
public import CORALean.ContDynamics.Interfaces
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# `LinearSys` and `LinearSys.WithInput` instantiate `ContDynamics` and `Reach`

`params` is `Reach.Params` at real time, `options` `ReachStepOptions`; `reachExact` is
each system's own on `[0, tFinal - tStart]`, the system being time-invariant. All of it is the
canonical form's, as CORA's `reach` runs on `canonicalForm`: a `U` is the combined input
`B U ⊕ c ⊕ E W` in state coordinates, and `LinearSys` alone reads `A`, its `reachExact` the
homogeneous flow. `LinearSys.WithInput` carries `U`, `0 ∈ U` among its fields; it asks the
representation to be convex and compact, what [1, Thm. 3.1]'s enclosure needs of `U` —
[1, Alg. 2]. `LinearSys.WithInputSplit` drops `0 ∈ U` and asks for `Recentre` and `OfPoint`
too — [1, Alg. 3]; it bundles `U` as well, the pair's type choosing the algorithm, as `P` and
`O` are the instance's outputs. Every run is `none` unless `0 < timeStep`.

`LinearSys` is the homogeneous case, asking none of this: a non-convex representation
reaches. `LinearSys.reachInstance` runs `reachAdmissible`, CORA's `standard` scheme and its
default — [1, Alg. 4], recursively — `none` also unless `tStart < tFinal` keeps a window, `η`
raised until admissible. `LinearSys.reachWrappingFreeInstance` is the same interface at
`reachWrappingFree`, [1, Alg. 1], a named `def` so resolution stays unambiguous.

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

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance LinearSys.reachInstance :
    Reach (LinearSys 𝕋) (fun n _ => Reach.Params (S n) ℝ) (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < params.tFinal - params.tStart ∧ 0 < options.Δt then
      some (sys.reachAdmissible params options)
    else none
  reach_outer sys params options _ hR := by
    -- `none` is equal to no `some R`, so only the run the side conditions admit is left
    split_ifs at hR with h
    cases hR
    exact sys.reachAdmissible_outer h.1 h.2

/-- Kept as a named `def` rather than an `instance`, so instance resolution stays
unambiguous between it and `LinearSys.reachInstance`. -/
@[reducible] noncomputable def LinearSys.reachWrappingFreeInstance :
    Reach (LinearSys 𝕋) (fun n _ => Reach.Params (S n) ℝ) (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reachWrappingFree params options) else none
  reach_outer sys params options _ hR := by
    -- `none` is equal to no `some R`, so only the run the side conditions admit is left
    split_ifs at hR with h
    cases hR
    exact sys.reachWrappingFree_outer params h

noncomputable instance LinearSys.WithInput.reachInstance
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinearSys.WithInput 𝕋 S) (fun n _ => Reach.Params (S n) ℝ)
      (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reach params options) else none
  reach_outer sys params options _ hR := by
    -- `none` is equal to no `some R`, so only the run the side conditions admit is left
    split_ifs at hR with h
    cases hR
    exact sys.reach_outer params h

noncomputable instance LinearSys.WithInputSplit.reachInstance
    [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinearSys.WithInputSplit 𝕋 S) (fun n _ => Reach.Params (S n) ℝ)
      (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reach params options) else none
  reach_outer sys params options _ hR := by
    -- `none` is equal to no `some R`, so only the run the side conditions admit is left
    split_ifs at hR with h
    cases hR
    exact sys.reach_outer params h

/-- CORA's `linearSys` as a `ContDynamics`: `B u` the input, `E w` the disturbance. -/
instance LinearSys.contDynamics {n : ℕ} : ContDynamics (LinearSys 𝕋 n) n where
  nrOfInputs sys := sys.m
  nrOfDisturbances sys := sys.r
  Trajectory sys T X₀ U W x u w :=
    ∃ v y, LinearSys.Trajectory (S := 𝒮) sys T X₀ U W Set.univ x u w v y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
