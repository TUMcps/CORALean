module

public import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono

@[expose] public section

/-!
# `inputSolution` contains the input's contribution at every time in the step

`inputSolution_outer` encloses what the input contributed where the step *ends*.
A time-interval enclosure needs one set covering every `t ∈ [0, r]`, and
[1, Prop. 3.3] says `0 ∈ U` makes those the same set — a statement about sets of
points, so it is the point system at the fixed member that carries it and the
matrix set never enters.

That is the whole of the extension: the member's `inputReach` grows with the
window, and `inputReach_subset_inputSolution` sends the longest window into the
enclosure computed from the box.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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
theorem LinParamSys.ConstTrajectory.inputSolution_timeInterval_outer
    {sys : LinParamSys ℐ n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}
    {A : Mat ℝ n n} {r : ℝ} (traj : sys.ConstTrajectory T R₀ U x u A)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) (η : ℕ)
    (hε : ‖(Interval.smul r sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r η) U)))
    -- `0 ∈ U` is what `inputReach_mono` needs, and the only extra hypothesis here
    (h0 : (0 : Vec ℝ n) ∈ construct U)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      ∈ construct (sys.inputSolution r η U) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  -- the fixed matrix names the point system where `inputReach` and its measurability live
  have lin := traj.toLinearSys
  have hmemt : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      ∈ (LinearSys.mk A : LinearSys ℝ n).inputReach U t :=
    ⟨u, fun s hs => traj.input s (hTt hs), lin.aestronglyMeasurable_input hTt,
      by simp only [Scalar.toRealMat_real]⟩
  exact sys.inputReach_subset_inputSolution hr η hε traj.param hconv hclosed hbdd
    hRconv hRclosed hRbdd
    ((LinearSys.mk A : LinearSys ℝ n).inputReach_mono hbdd h0 ht0 htr hmemt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
