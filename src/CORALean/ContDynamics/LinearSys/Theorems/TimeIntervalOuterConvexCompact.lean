module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterInputSolution
public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.ContSet.Definitions.ConvexSet

@[expose] public section

/-!
# The step enclosure at any convex, compact representation

`timeInterval_outer_inputSolution` with its six topological hypotheses read off
the representation, exactly as `ReachOuterConvexCompact` does at the sample
times.

`0 ∈ U` stays a hypothesis: it is a fact about where the input set sits, not
about its shape, so no class can supply it. The first case of [1, Alg. 2], the only one
with a single enclosure for the whole step; the second case splits `U` instead
and needs a representation that can recenter itself.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every trajectory whose input set is convex, compact and contains the origin
stays in the step enclosure at every time of the step, not only at its end. -/
theorem LinearSys.IsCanonicalTrajectory.timeInterval_outer_convexCompact
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) (h0 : (0 : Vec ℝ n) ∈ construct U) : -- --- STMT ---
    x t ∈ construct (Plus.plus
      (sys.timeIntervalStep r (m + 2) R₀) (sys.inputSolution r (m + 2) U)) :=
  traj.timeInterval_outer_inputSolution hr hT hε ht0 htr
    (ConvexSet.convex_construct U) (CompactSet.isClosed_construct U)
    (CompactSet.isBounded_construct U)
    (ConvexSet.convex_construct _) (CompactSet.isClosed_construct _)
    (CompactSet.isBounded_construct _) h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
