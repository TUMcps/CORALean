import CORALean.ContDynamics.LinearSys.Theorems.ReachSetSubsetTimeIntervalInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalReachSetEqUnion

/-!
# One computed set encloses the whole interval's reachable set at once

`reachSet_subset_timeInterval_inputSolution` read at every time of `[0, r]`
together, through `timeIntervalReachSet_eq_iUnion`: the per-time statement and
this one carry the same content, but this one names no time at all, which is
the point of having `timeIntervalReachSet` in the first place.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to enclose the whole interval's reachable set in one
inclusion; for `reachSet_subset_timeInterval_inputSolution` where a single
time is what is in hand. -/
theorem LinearSys.timeIntervalReachSet_subset_timeInterval_inputSolution
    (sys : LinearSys 𝕋 n) {T : Set ℝ} (R₀ U : S n) {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T)
    {m : ℕ} (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U) :
    sys.timeIntervalReachSet T R₀ U r ⊆ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀)
      (sys.inputSolution r (m + 2) U)) := by
  rw [sys.timeIntervalReachSet_eq_iUnion]
  refine Set.iUnion₂_subset fun t ht => ?_
  exact sys.reachSet_subset_timeInterval_inputSolution R₀ U hr hT hε hconv hclosed hbdd
    hRconv hRclosed hRbdd h0 ht.1 ht.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
