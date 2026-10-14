module

public import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryInputSolutionTimeIntervalOuterSplit
public import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryTimeIntervalOuter
public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint

@[expose] public section

/-!
# The step enclosure at a box whose input set misses the origin

`ConstTrajectoryTimeIntervalOuterInputSolution` needs `0 ∈ U`, which no
representation has to satisfy. `Recentre` takes the input set apart into a
centre and a remainder holding the origin, `OfPoint` gives the constant its own
singleton, and `linComb (ofPoint 0) (ofPoint c)` is the segment the constant is
enclosed against, exactly as the point-matrix split does it, so no
representation-specific development is needed here either.

That is `R(0)` of [1, Alg. 4] and nothing beyond it: the enclosure over one step
`[0,r]`, at every matrix the box holds; the loop over the horizon is
`discretizeEnclosure_mem_reach`. The printed line subtracts `P̃(r) = C(r)ũ`
inside the hull and adds it back, which cancels only where `P̃(r)` is a point —
true at a point matrix, false at a box, where `C(r)` is itself an interval
matrix. The segment does that work with no subtraction to cancel.

`Mtimes (Mat ℝ) S` is not asked for, where the point case needs it: every factor
is now an interval matrix, `C(r)` included.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

-- the six shape hypotheses are asked of the remainder products, not of the sets they multiply
/-- A constant-parameter run stays in the step enclosure at every time of the
step, wherever the input set sits. -/
theorem LinParamSys.CanonicalConstTrajectory.timeInterval_outer_split
    [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    {sys : LinParamSys ℐ n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}
    {A : Mat ℝ n n} {r : ℝ} (traj : sys.CanonicalConstTrajectory T R₀ U x u A)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x t ∈ construct (Plus.plus
      (sys.timeIntervalStep r (m + 2) R₀)
      (Plus.plus
        (Plus.plus
          (sys.inputSolution r (m + 2) (LinComb.linComb
            (OfPoint.ofPoint (0 : Vec ℝ n)) (OfPoint.ofPoint (Recentre.centre U))))
          (Mtimes.mtimes (𝕄 := ℐ)
            (MatExp.intervalConstCorrectionMatrix sys.A r (m + 2))
            (OfPoint.ofPoint (Recentre.centre U))))
        (sys.inputSolution r (m + 2) (Recentre.recentre U)))) :=
  -- every hypothesis comes off `Recentre`/`OfPoint`, which is why no representation is named
  traj.timeInterval_outer hr hT hε ht0 htr (CompactSet.isBounded_construct U)
    (traj.inputSolution_timeInterval_outer_split hr hT (m + 2) hε
      (fun _ hy => Recentre.sub_centre_mem_recentre hy)
      (OfPoint.mem_ofPoint (Recentre.centre U))
      (fun _ hlam => smul_mem_linComb_ofPoint (Recentre.centre U) hlam)
      (CompactSet.isBounded_construct (OfPoint.ofPoint (Recentre.centre U)))
      (ConvexSet.convex_construct (LinComb.linComb
        (OfPoint.ofPoint (0 : Vec ℝ n)) (OfPoint.ofPoint (Recentre.centre U))))
      (CompactSet.isClosed_construct (LinComb.linComb
        (OfPoint.ofPoint (0 : Vec ℝ n)) (OfPoint.ofPoint (Recentre.centre U))))
      (CompactSet.isBounded_construct (LinComb.linComb
        (OfPoint.ofPoint (0 : Vec ℝ n)) (OfPoint.ofPoint (Recentre.centre U))))
      -- the tail of `C(r)` meets the segment, so the shape is asked of that product
      (ConvexSet.convex_construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A r (m + 2)) (LinComb.linComb
          (OfPoint.ofPoint (0 : Vec ℝ n)) (OfPoint.ofPoint (Recentre.centre U)))))
      (CompactSet.isClosed_construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A r (m + 2)) (LinComb.linComb
          (OfPoint.ofPoint (0 : Vec ℝ n)) (OfPoint.ofPoint (Recentre.centre U)))))
      (CompactSet.isBounded_construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A r (m + 2)) (LinComb.linComb
          (OfPoint.ofPoint (0 : Vec ℝ n)) (OfPoint.ofPoint (Recentre.centre U)))))
      -- and the recentred set is what Prop. 3.3 is read at
      (Recentre.zero_mem_recentre U)
      (ConvexSet.convex_construct (Recentre.recentre U))
      (CompactSet.isClosed_construct (Recentre.recentre U))
      (CompactSet.isBounded_construct (Recentre.recentre U))
      -- its own remainder product, the same three facts again
      (ConvexSet.convex_construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A r (m + 2)) (Recentre.recentre U)))
      (CompactSet.isClosed_construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A r (m + 2)) (Recentre.recentre U)))
      (CompactSet.isBounded_construct (Mtimes.mtimes (𝕄 := ℐ)
        (MatExp.intervalInputRemainder sys.A r (m + 2)) (Recentre.recentre U)))
      ht0 htr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
