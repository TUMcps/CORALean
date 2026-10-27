module

public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSetExact
public import CORALean.ContDynamics.LinearSys.Definitions.StepInner
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInnerRep
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalSubsetInitialAddError
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

@[expose] public section

/-!
# The whole-step inner approximation lands in the exact tube

`timeIntervalInner_inner` at the reachable set over `[0, r]`, for any input set `U`. The inner
approximation lies in `X₀` itself (`timeInterval_subset_initial_add_error` measures against
`X₀`), and every point of `X₀` is the state at `t = 0` of a Carathéodory run on `[0, r]`: hold the
input at `U`'s center and take `closedForm`, which `closedForm_flow` makes an
`IsCanonicalTrajectory`. `timeInterval` carries no input, so `U` enters only through that witness; a
zonotope is never empty, so no hypothesis on `U` is needed.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `X₀` – initial zonotope
* `U` – input zonotope

## Hypotheses
* `hr` – step length positive
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* the enclosure minus the error ball lies inside the exact interval reach set
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The step's enclosure minus its own error ball is *contained in* the states
the system visits over `[0, r]`, under inputs in any `U`. -/
theorem LinearSys.timeIntervalInner_subset_timeIntervalReachSetExact
    (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (X₀ U : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    sys.timeIntervalInner r η X₀
      ⊆ sys.timeIntervalReachSetExact (S := 𝒵) (Set.Icc 0 r) X₀ U r := by -- --- PROOF ---
  have hOuter := sys.timeInterval_subset_initial_add_error hr η hε X₀
  -- the error ball holds a point because it encloses the step's own center
  have hEne : (Metric.closedBall (0 : Vec ℝ n) (sys.timeIntervalStepError r η X₀)).Nonempty := by
    obtain ⟨_, _, e, he, _⟩ := hOuter (Zonotope.center_mem_construct _)
    exact ⟨e, he⟩
  have hinner := minkowskiDiff_inner_of_outer hEne Metric.isBounded_closedBall
    (Zonotope.convex_construct X₀) (Zonotope.isCompact_construct X₀).isClosed hOuter
  intro y hy
  -- the run from `y` under the input held at `U`'s center, read at `t = 0`
  have hU := Zonotope.isBounded_construct U
  have hu : ∀ s ∈ Set.Icc (0:ℝ) r, (fun _ => U.c) s ∈ construct U :=
    fun _ _ => Zonotope.center_mem_construct U
  have hmeas : AEStronglyMeasurable (fun _ : ℝ => U.c) (volume.restrict (Set.Icc 0 r)) :=
    aestronglyMeasurable_const
  have traj : sys.IsCanonicalTrajectory (S := 𝒵) (Set.Icc 0 r) X₀ U
      (sys.closedForm y fun _ => U.c) (fun _ => U.c) :=
    ⟨by rw [sys.closedForm_zero]; exact hinner hy, hu, hmeas,
      sys.closedForm_continuousOn (S := 𝒵) y hr.le hU hu hmeas,
      fun τ hτ => sys.closedForm_flow (S := 𝒵) y hr.le hU hu hmeas hτ⟩
  exact ⟨_, _, traj, 0, Set.left_mem_Icc.mpr hr.le, sys.closedForm_zero y _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
