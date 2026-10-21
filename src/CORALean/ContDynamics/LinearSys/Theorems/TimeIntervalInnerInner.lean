module

public import CORALean.ContDynamics.LinearSys.Definitions.StepInner
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInnerRep
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalSubsetInitialAddError
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffInnerOfOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

@[expose] public section

/-!
# The same over a whole step

`timePointStepInner_inner` at the time-interval step: what the step computes minus its own error
ball is contained in the states the flow visits over the step. The hull gap does not block this: the
union over `t ∈ [0, r]` is a union of images and need not be convex, so the bridge cannot be applied
at it; but the outer bound that carries the estimate, `timeInterval_subset_initial_add_error`,
measures against `X₀` alone, a zonotope. So the bridge lands inside `X₀`, and `t = 0` puts that
inside the union. The price is exactly the price of the gap: the inner approximation is inside the
*initial* set, not merely inside the tube, and coarse because `timeIntervalStepError` is first order
in the step where the correction it is meant to pay for is second; only a shorter step improves it.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `X₀` – initial zonotope

## Hypotheses
* `hr` – step length positive
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* the enclosure minus the error ball lies inside the states the flow visits over the step
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The step's enclosure minus its own error ball is *contained in* the states
the flow visits over the step. -/
theorem LinearSys.timeIntervalInner_inner (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r)
    (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (X₀ : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    sys.timeIntervalInner r η X₀
      ⊆ ⋃ t ∈ Set.Icc (0:ℝ) r,
          (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' X₀.construct := by -- --- PROOF ---
  have hOuter := sys.timeInterval_subset_initial_add_error hr η hε X₀
  -- the error ball holds a point because it encloses the step's own center
  have hEne : (Metric.closedBall (0 : Vec ℝ n) (sys.timeIntervalStepError r η X₀)).Nonempty := by
    obtain ⟨_, _, e, he, _⟩ := hOuter (Zonotope.center_mem_construct _)
    exact ⟨e, he⟩
  have hinner := minkowskiDiff_inner_of_outer hEne Metric.isBounded_closedBall
    (Zonotope.convex_construct X₀) (Zonotope.isCompact_construct X₀).isClosed hOuter
  -- and the start of the step is one of the times the flow is taken over
  intro y hy
  refine Set.mem_biUnion (Set.left_mem_Icc.mpr hr.le) ⟨y, hinner hy, ?_⟩
  show exp ((0:ℝ) • toRealMat sys.A) *ᵥ y = y
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
