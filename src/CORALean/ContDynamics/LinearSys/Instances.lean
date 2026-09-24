import CORALean.ContDynamics.LinearSys.Definitions.ReachParams
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterWindows
import CORALean.ContDynamics.LinearSys.Theorems.WithInputReachOuter
import CORALean.ContDynamics.LinearSys.Theorems.WithInputSplitReachOuter
import CORALean.ContDynamics.Reach.Reach
import CORALean.ContSet.Interval.Real.Instances

/-!
# `LinearSys` and `LinearSys.WithInput` instantiate `Reach`

`reachExact`, `reach` and `reach_outer` are each system's own, at the horizon,
window width and Taylor order `Params` holds; `reach` is always `some`, nothing
here failing at run time. `LinearSys.WithInput` carries the input set, `0 ∈ U`
among its fields, and asks the representation to be convex and compact, what
[1, Thm. 3.1]'s enclosure needs of `U` — [1, Alg. 2]. `LinearSys.WithInputSplit`
drops `0 ∈ U` and asks for `Recentre` and `OfPoint` too — [1, Alg. 3].
`LinearSys` is the homogeneous case, kept because it asks for none of these: a
non-convex representation still reaches.

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

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance LinearSys.reachInstance : Reach (LinearSys 𝕋) LinearSys.ReachParams S where
  reachExact sys p X₀ := sys.reachExact p.tFinal X₀
  reach sys p X₀ := some (sys.reach p.tFinal p.Δt p.η X₀)
  reach_outer sys p X₀ := sys.reach_outer p.hΔt X₀

noncomputable instance LinearSys.WithInput.reachInstance
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinearSys.WithInput 𝕋 S) LinearSys.ReachParams S where
  reachExact sys p X₀ := sys.reachExact p.tFinal X₀
  reach sys p X₀ := some (sys.reach p.tFinal p.Δt p.η X₀)
  reach_outer sys p X₀ := sys.reach_outer p.hΔt X₀

noncomputable instance LinearSys.WithInputSplit.reachInstance
    [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)] :
    Reach (LinearSys.WithInputSplit 𝕋 S) LinearSys.ReachParams S where
  reachExact sys p X₀ := sys.reachExact p.tFinal X₀
  reach sys p X₀ := some (sys.reach p.tFinal p.Δt p.η X₀)
  reach_outer sys p X₀ := sys.reach_outer p.hΔt X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
