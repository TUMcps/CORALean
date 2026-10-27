module

public import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryInputSolutionTimeIntervalOuterSplit
public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryTimeIntervalOuter
public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.ContSet.Theorems.SmulMemLinCombOfPoint

@[expose] public section

/-!
# The step enclosure at a box whose input set misses the origin

`ConstTrajectoryTimeIntervalOuterInputSolution` needs `0 ∈ U`, which no representation has to
satisfy. `Recenter` takes the input set apart into a center and a remainder holding the origin,
`OfPoint` gives the constant its own singleton, and `linComb (ofPoint 0) (ofPoint c)` is the
segment the constant is enclosed against. That is `R_0` of [1, Alg. 1], extended to an input set
missing the origin: the enclosure over one step `[0,r]`, at every matrix the box holds; the loop
over the horizon is `discretizeEnclosure_mem_reach`. The point-matrix construction subtracts
`P̃(r) = C(r)ũ` inside the hull and adds it back, which cancels only where `P̃(r)` is a point; the
segment does that work with no subtraction to cancel.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal
* `A` – system matrix member
* `r` – step size
* `m` – Taylor order minus two
* `t` – time

## Hypotheses
* `traj` – constant-parameter trajectory
* `hr` – step positive
* `hT` – step lies in the time set
* `hε` – order admissible
* `ht0` – time nonnegative
* `htr` – time at most the step

## Conclusion
* the state at time `t` lies in the step enclosure for the split input set

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
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
theorem LinParamSys.IsCanonicalConstTrajectory.timeInterval_outer_split
    [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)]
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    {sys : LinParamSys ℐ n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}
    {A : Mat ℝ n n} {r : ℝ} (traj : sys.IsCanonicalConstTrajectory T R₀ U x u A)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x t ∈ construct (Plus.plus
      (sys.timeInterval r (m + 2) R₀)
      (Plus.plus
        (Plus.plus
          (sys.inputSolution r (m + 2) (LinComb.linComb
            (OfPoint.ofPoint (0 : Vec ℝ n)) (OfPoint.ofPoint (Recenter.center U))))
          (Mtimes.mtimes (𝕄 := ℐ)
            (MatExp.intervalConstCorrectionMatrix sys.A r (m + 2))
            (OfPoint.ofPoint (Recenter.center U))))
        (sys.inputSolution r (m + 2) (Recenter.recenter U)))) :=
  -- the segment from `0` to the center, and its product with the remainder
  let seg : S n := LinComb.linComb (OfPoint.ofPoint (0 : Vec ℝ n))
    (OfPoint.ofPoint (Recenter.center U))
  let rem : S n := Mtimes.mtimes (𝕄 := ℐ) (MatExp.intervalInputRemainder sys.A r (m + 2)) seg
  -- the remainder's product with the recentered set
  let rem₂ : S n := Mtimes.mtimes (𝕄 := ℐ) (MatExp.intervalInputRemainder sys.A r (m + 2))
    (Recenter.recenter U)
  -- every hypothesis comes off `Recenter`/`OfPoint`, which is why no representation is named
  traj.timeInterval_outer hr hT hε ht0 htr (CompactSet.isBounded_construct U)
    (traj.inputSolution_timeInterval_outer_split hr hT (m + 2) hε
      (fun _ hy => Recenter.sub_center_mem_recenter hy)
      (OfPoint.mem_ofPoint (Recenter.center U))
      (fun _ hlam => smul_mem_linComb_ofPoint (Recenter.center U) hlam)
      (CompactSet.isBounded_construct (OfPoint.ofPoint (Recenter.center U)))
      (ConvexSet.convex_construct seg)
      (CompactSet.isClosed_construct seg)
      (CompactSet.isBounded_construct seg)
      -- the tail of `C(r)` meets the segment, so the shape is asked of that product
      (ConvexSet.convex_construct rem)
      (CompactSet.isClosed_construct rem)
      (CompactSet.isBounded_construct rem)
      -- and the recentered set is what [1, Sec. 3.3] is read at
      (Recenter.zero_mem_recenter U)
      (ConvexSet.convex_construct (Recenter.recenter U))
      (CompactSet.isClosed_construct (Recenter.recenter U))
      (CompactSet.isBounded_construct (Recenter.recenter U))
      -- its own remainder product, the same three facts again
      (ConvexSet.convex_construct rem₂)
      (CompactSet.isClosed_construct rem₂)
      (CompactSet.isBounded_construct rem₂)
      ht0 htr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
