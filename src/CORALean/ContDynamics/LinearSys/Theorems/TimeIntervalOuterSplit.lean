import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuterSplit
import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint

/-!
# The step enclosure at a set whose input set misses the origin

`timeInterval_outer_convexCompact` needs `0 ∈ U`, which no representation has
to satisfy. `Recentre` takes the input set apart into a centre and a
remainder holding the origin, and `OfPoint` gives the constant its own
singleton; `linComb (ofPoint 0) (ofPoint c)` is then the segment the constant
is enclosed against, so no representation-specific development is needed.

So [1, Alg. 3] — the extension of [1, Alg. 2] to an input set not containing
the origin, split into a constant part and a zero-containing remainder —
assumes nothing at all about where the input set sits, at every representation
with a centre.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, Reduce (S n) (Vec ℝ n)] in
-- twelve arguments in one term, each elaborating a `Mtimes` instance at `S` or `ℐ`
set_option maxHeartbeats 400000 in
/-- Every trajectory stays in the step enclosure at every time of the step,
wherever the input set sits. -/
theorem LinearSys.Trajectory.timeInterval_outer_split [Mtimes ℐ S] [∀ n, OfPoint (S n) (Vec ℝ n)]
    [∀ n, Recentre (S n) (Vec ℝ n)] [∀ n, ConvexSet (S n) (Vec ℝ n)]
    [∀ n, CompactSet (S n) (Vec ℝ n)]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.Trajectory T R₀ U x u) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x t ∈ construct (Plus.plus
      (sys.timeIntervalStep r (m + 2) R₀)
      (Plus.plus
        (Plus.plus
          (Mtimes.mtimes (𝕄 := Mat ℝ)
            (MatExp.expIntegral (toRealMat sys.A) r)
            (LinComb.linComb (OfPoint.ofPoint (0 : Vec ℝ n))
              (OfPoint.ofPoint (Recentre.centre U))))
          (Mtimes.mtimes (𝕄 := ℐ)
            (MatExp.constCorrectionMatrix (toRealMat sys.A) r (m + 2))
            (OfPoint.ofPoint (Recentre.centre U))))
        (sys.inputSolution r (m + 2) (Recentre.recentre U)))) :=
  -- every hypothesis comes off `Recentre`/`OfPoint`, which is why this needs no representation
  traj.timeInterval_outer hr hT hε ht0 htr (CompactSet.isBounded_construct U)
    (traj.inputSolution_timeInterval_outer_split hr hT (m + 2) hε
      (fun _ hy => Recentre.sub_centre_mem_recentre hy)
      (OfPoint.mem_ofPoint (Recentre.centre U))
      (fun _ hlam => smul_mem_linComb_ofPoint (Recentre.centre U) hlam)
      (CompactSet.isBounded_construct (OfPoint.ofPoint (Recentre.centre U)))
      (Recentre.zero_mem_recentre U)
      (ConvexSet.convex_construct (Recentre.recentre U))
      (CompactSet.isClosed_construct (Recentre.recentre U))
      (CompactSet.isBounded_construct (Recentre.recentre U))
      (ConvexSet.convex_construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) (Recentre.recentre U)))
      (CompactSet.isClosed_construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) (Recentre.recentre U)))
      (CompactSet.isBounded_construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) (Recentre.recentre U)))
      ht0 htr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
