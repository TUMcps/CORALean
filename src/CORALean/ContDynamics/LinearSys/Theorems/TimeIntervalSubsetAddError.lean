module

public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalSubsetInitialAddError

@[expose] public section

/-!
# What the step encloses beyond what the flow visits

`timeInterval_outer` run backwards, and the direction an error measure needs: the computed set
is inside the states the flow visits over the step, widened by a ball.
`timeInterval_subset_initial_add_error` is where the estimate is done, and it is sharper: the
exact point it names is the state at `t = 0`, so it measures against `X₀` alone. This weakens that
to the union over the step, which is the shape every outer statement about the step is stated in, at
the cost of a right-hand side that is a union of images and so need not be convex; an inner
approximation goes through the sharper form and never this one.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `X₀` – initial zonotope

## Hypotheses
* `hr` – step length positive
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* the computed step lies in the visited states widened by the error
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

/-- The reverse of `timeInterval_outer`: what the step computes stays inside
what the flow visits over it, widened by `timeIntervalStepError`. -/
theorem LinearSys.timeInterval_subset_reach_add_error (sys : LinearSys 𝕋 n) {r : ℝ}
    (hr : 0 < r) (η : ℕ) (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (X₀ : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    (sys.timeInterval (S := 𝒵) r η X₀).construct
      ⊆ (⋃ t ∈ Set.Icc (0:ℝ) r,
            (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' X₀.construct)
        + Metric.closedBall (0 : Vec ℝ n)
            (sys.timeIntervalStepError r η X₀) := by -- --- PROOF ---
  intro y hy
  obtain ⟨x, hx, e, he, rfl⟩ := sys.timeInterval_subset_initial_add_error hr η hε X₀ hy
  -- the start of the step is one of the times the flow is taken over
  refine ⟨x, Set.mem_biUnion (Set.left_mem_Icc.mpr hr.le) ⟨x, hx, ?_⟩, e, he, rfl⟩
  show exp ((0:ℝ) • toRealMat sys.A) *ᵥ x = x
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
