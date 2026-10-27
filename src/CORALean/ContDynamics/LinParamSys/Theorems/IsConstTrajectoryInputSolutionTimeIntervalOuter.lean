module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.IntervalInputRemainderSet

@[expose] public section

/-!
# `inputSolution` contains the input's contribution at every time in the step

`inputSolution_outer` encloses what the input contributed where the step *ends*. A time-interval
enclosure needs one set covering every `t ∈ [0, r]`, and [1, Sec. 3.3] says `0 ∈ U` makes those
the same set — a statement about sets of points, so it is the point system at the fixed member
that carries it and the matrix set never enters. The member's `inputReach` grows with the
window, and `inputReach_subset_inputSolution` sends the longest window into the enclosure
computed from the box.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – input signal
* `A` – system matrix member
* `r` – step size
* `η` – Taylor order
* `t` – time

## Hypotheses
* `traj` – constant-parameter trajectory
* `hr` – step positive
* `hT` – step lies in the time set
* `hε` – order admissible
* `hconv` – input set convex
* `hclosed` – input set closed
* `hbdd` – input set bounded
* `hRconv` – remainder image convex
* `hRclosed` – remainder image closed
* `hRbdd` – remainder image bounded
* `h0` – origin lies in the input set
* `ht0` – time nonnegative
* `htr` – time at most the step

## Conclusion
* the input's contribution up to time `t` lies in the enclosure

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
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
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Everything a constant-parameter run's input contributed up to any time in
the step lies in the enclosure computed for the whole step. -/
theorem LinParamSys.IsCanonicalConstTrajectory.inputSolution_timeInterval_outer
    {sys : LinParamSys ℐ n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}
    {A : Mat ℝ n n} {r : ℝ} (traj : sys.IsCanonicalConstTrajectory T R₀ U x u A)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) (η : ℕ)
    (hε : ‖(Interval.smul r sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (MatExp.intervalInputRemainderSet sys.A r η U))
    (hRclosed : IsClosed (MatExp.intervalInputRemainderSet sys.A r η U))
    (hRbdd : Bornology.IsBounded (MatExp.intervalInputRemainderSet sys.A r η U))
    -- `0 ∈ U` is what `inputReach_mono` needs, and the only extra hypothesis here
    (h0 : (0 : Vec ℝ n) ∈ construct U)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- CONCL ---
    (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      ∈ construct (sys.inputSolution r η U) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  -- the fixed matrix names the point system where `inputReach` and its measurability live
  have lin := traj.toLinearSys
  have hmemt : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      ∈ (LinearSys.canonical A : LinearSys ℝ n).inputReach U t :=
    ⟨u, fun s hs => traj.input s (hTt hs), lin.aestronglyMeasurable_input hTt,
      by simp only [Scalar.toRealMat_real]⟩
  exact sys.inputReach_subset_inputSolution hr η hε traj.param hconv hclosed hbdd
    hRconv hRclosed hRbdd
    ((LinearSys.canonical A : LinearSys ℝ n).inputReach_mono hbdd h0 ht0 htr hmemt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
