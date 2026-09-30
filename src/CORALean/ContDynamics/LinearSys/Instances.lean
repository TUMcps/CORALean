import CORALean.ContDynamics.LinearSys.Theorems.ReachAdmissibleOuter
import CORALean.ContDynamics.LinearSys.Theorems.ReachWrappingFreeOuter
import CORALean.ContDynamics.LinearSys.Theorems.WithInputReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.WithInputSplitReachOuter
import CORALean.ContDynamics.Reach.Reach
import CORALean.ContSet.Interval.Real.Instances

/-!
# `LinearSys` and `LinearSys.WithInput` instantiate `Reach`

`params` is `Reach.Params` at real time, `options` `ReachStepOptions`; `reachExact` is
each system's own on `[0, tFinal - tStart]`, the system being time-invariant.
`LinearSys.WithInput` carries the input set, `0 ∈ U` among its fields, so `U` is the
system's rather than `params`'; it asks the representation to be convex and compact,
what [1, Thm. 3.1]'s enclosure needs of `U` — [1, Alg. 2]. `LinearSys.WithInputSplit`
drops `0 ∈ U` and asks for `Recentre` and `OfPoint` too — [1, Alg. 3]; it bundles `U`
as well, the pair's type choosing the algorithm, as `P` and `O` are the instance's
outputs. Every run is `none` unless `0 < timeStep`, which every theorem here asks.

`LinearSys` is the homogeneous case, kept because it asks for none of these: a
non-convex representation still reaches. `LinearSys.reachInstance` runs
`reachAdmissible`, CORA's `standard` scheme and its default — [1, Alg. 4],
recursively — `none` also unless `tStart < tFinal` keeps a window, `taylorTerms`
raised until admissible. `LinearSys.reachWrappingFreeInstance` is the same interface
at `reachWrappingFree`, [1, Alg. 1]'s window-by-window construction, kept as a
named `def` rather than an `instance` so resolution stays unambiguous.

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

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance LinearSys.reachInstance :
    Reach (LinearSys 𝕋) (fun n => Reach.Params (S n) ℝ) (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachExact (params.tFinal - params.tStart) (construct params.R0)
  reach sys params options :=
    if 0 < params.tFinal - params.tStart ∧ 0 < options.timeStep then
      some (sys.reachAdmissible params options)
    else none
  reach_outer sys params options := by
    -- `none` claims nothing, and `some` is the run the side conditions admit
    split_ifs with h
    · exact sys.reachAdmissible_outer h.1 h.2
    · trivial

/-- Kept as a named `def` rather than an `instance`, so instance resolution stays
unambiguous between it and `LinearSys.reachInstance`. -/
@[reducible] noncomputable def LinearSys.reachWrappingFreeInstance :
    Reach (LinearSys 𝕋) (fun n => Reach.Params (S n) ℝ) (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachExact (params.tFinal - params.tStart) (construct params.R0)
  reach sys params options :=
    if 0 < options.timeStep then some (sys.reachWrappingFree params options) else none
  reach_outer sys params options := by
    -- `none` claims nothing, and `some` is the run the side conditions admit
    split_ifs with h
    · exact sys.reachWrappingFree_outer params h
    · trivial

noncomputable instance LinearSys.WithInput.reachInstance
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinearSys.WithInput 𝕋 S) (fun n => Reach.Params (S n) ℝ)
      (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachExact (params.tFinal - params.tStart) (construct params.R0)
  reach sys params options :=
    if 0 < options.timeStep then some (sys.reach params options) else none
  reach_outer sys params options := by
    -- `none` claims nothing, and `some` is the run the side conditions admit
    split_ifs with h
    · exact sys.reach_outer params h
    · trivial

noncomputable instance LinearSys.WithInputSplit.reachInstance
    [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinearSys.WithInputSplit 𝕋 S) (fun n => Reach.Params (S n) ℝ)
      (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachExact (params.tFinal - params.tStart) (construct params.R0)
  reach sys params options :=
    if 0 < options.timeStep then some (sys.reach params options) else none
  reach_outer sys params options := by
    -- `none` claims nothing, and `some` is the run the side conditions admit
    split_ifs with h
    · exact sys.reach_outer params h
    · trivial

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
