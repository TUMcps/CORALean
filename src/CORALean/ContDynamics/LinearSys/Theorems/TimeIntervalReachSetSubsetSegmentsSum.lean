import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalReachSetEqUnion
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepOuterSegments
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# The time-interval reachable set inside an exact sum, not a representation

`timeIntervalReachSet_subset_timeInterval_inputSolution` encloses [1, Def. 3.2]'s
`R̂(τ_k)` with `construct (Plus.plus (timeIntervalStep ...) (inputSolution ...))`: an
operation whose only guarantee is `⊆`, so a bound on it cannot be assembled
from bounds on the two operands (`exists_outer_without_supportBound`). This is
the same content one step earlier, where `+` is the genuine Minkowski sum and
`segments` the genuine hull — everything `LinearSys.timeIntervalBound` needs.

Built the same way, off `timeIntervalStep_outer_segments` in place of
`timeIntervalStep_outer` and no further lift at the top.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to enclose the whole interval's reachable set by a genuine
sum of segments and sets; for `timeIntervalReachSet_subset_timeInterval_inputSolution`
where a computed representation is what is wanted instead. -/
theorem LinearSys.timeIntervalReachSet_subset_segments_sum (sys : LinearSys 𝕋 n) {T : Set ℝ}
    (R₀ U : S n) {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U) :
    sys.timeIntervalReachSet T R₀ U r
      ⊆ segments (construct R₀) ((exp (r • toRealMat sys.A)).mulVecLin '' construct R₀)
        + construct (Mtimes.mtimes (𝕄 := ℐ)
            (MatExp.correctionMatrix (toRealMat sys.A) r (m + 2)) R₀)
        + construct (sys.inputSolution r (m + 2) U) := by -- --- PROOF ---
  rw [sys.timeIntervalReachSet_eq_iUnion]
  refine Set.iUnion₂_subset fun t ht => ?_
  rintro _ ⟨x, u, traj, rfl⟩
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 ht.2⟩
  have hvoc := traj.variation_of_constants hTt le_rfl ht.1 hbdd
  rw [sub_zero] at hvoc
  rw [hvoc]
  exact Set.add_mem_add
    (sys.timeIntervalStep_outer_segments hr hε R₀ ht.1 ht.2 (Set.mem_image_of_mem _ traj.init))
    (traj.inputSolution_timeInterval_outer hr hT (m + 2) hε hconv hclosed hbdd hRconv hRclosed
      hRbdd h0 ht.1 ht.2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
