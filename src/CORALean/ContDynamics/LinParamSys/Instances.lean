import CORALean.ContDynamics.LinParamSys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.WithInputReachUnionOuter
import CORALean.ContDynamics.LinParamSys.Theorems.WithInputSplitReachUnionOuter
import CORALean.ContDynamics.Reach.Reach

/-!
# `LinParamSys ℐ`, `LinParamSys.WithInput` and `WithInputSplit` instantiate `Reach`

`params` is `Reach.Params` at real time, `options` `LinearSys.ReachStepOptions`, the
point case's. `reachExact` is `reachUnionExact` on `[0, tFinal - tStart]`, the system
being time-invariant, `reach` is `reachUnion`, `none` unless `0 < Δt`, and the
guarantee is `reachUnion_outer`, for each — constant-parameter, in
`⌈(tFinal - tStart) / Δt⌉` windows. `LinParamSys ℐ` is homogeneous;
`LinParamSys.WithInput` carries the input set, `0 ∈ U` among its fields, so `U` is the
system's rather than `params`', and asks the representation to be convex and compact,
what `inputSolution`'s enclosure needs of `U`; `LinParamSys.WithInputSplit` drops
`0 ∈ U` and asks for `Recentre` too — [1, Alg. 4]'s split case.

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

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance LinParamSys.reachInstance :
    Reach (LinParamSys ℐ) (fun n => Reach.Params (S n) ℝ) (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reachUnion params options) else none
  reach_outer sys params options := by
    -- `none` claims nothing, and `some` is the run the side conditions admit
    split_ifs with h
    · exact sys.reachUnion_outer params h
    · trivial

noncomputable instance LinParamSys.WithInput.reachInstance
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinParamSys.WithInput S) (fun n => Reach.Params (S n) ℝ)
      (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reachUnion params options) else none
  reach_outer sys params options := by
    -- `none` claims nothing, and `some` is the run the side conditions admit
    split_ifs with h
    · exact sys.reachUnion_outer params h
    · trivial

noncomputable instance LinParamSys.WithInputSplit.reachInstance
    [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinParamSys.WithInputSplit S) (fun n => Reach.Params (S n) ℝ)
      (LinearSys.ReachStepOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt then some (sys.reachUnion params options) else none
  reach_outer sys params options := by
    -- `none` claims nothing, and `some` is the run the side conditions admit
    split_ifs with h
    · exact sys.reachUnion_outer params h
    · trivial

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
