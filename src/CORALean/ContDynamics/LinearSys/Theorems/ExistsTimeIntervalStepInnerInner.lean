module

public import CORALean.ContDynamics.LinearSys.Theorems.ExistsTimeIntervalStepErrorLt
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepInnerInner
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono

@[expose] public section

/-!
# The same over a whole step

`ExistsTimePointStepInnerInner` at the time-interval step: for every `ε > 0`
there is a step at which taking off the ball of radius `ε` already yields an
inner approximation of the states the flow visits over it.

The step produced is shorter than the one at the step's end, and for a reason
that survives here: `timeIntervalStepError` is first order in the step, so
driving it under `ε` costs a step of order `ε` where the point error, second
order, needs only `√ε`. The order helps at neither.
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

/-- Some step is short enough that its enclosure minus a ball of the caller's
own radius `ε` is already inside the states the flow visits over it. -/
theorem LinearSys.exists_timeIntervalStepInner_inner (sys : LinearSys 𝕋 n)
    (X₀ : Zonotope (Vec ℝ n)) (η : ℕ) {ε : ℝ} (hε : 0 < ε) : -- --- STMT ---
    ∃ r : ℝ, 0 < r ∧ sys.timeIntervalStepError r η X₀ < ε ∧
      minkowskiDiff (sys.timeIntervalStep (S := 𝒵) r η X₀).construct
          (Metric.closedBall (0 : Vec ℝ n) ε)
        ⊆ ⋃ t ∈ Set.Icc (0:ℝ) r,
            (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' X₀.construct := by -- --- PROOF ---
  obtain ⟨r, hr, herr, hside⟩ := sys.exists_timeIntervalStepError_lt X₀ η hε
  refine ⟨r, hr, herr, ?_⟩
  -- the true error is under the tolerance, so its ball is inside the one taken off
  refine subset_trans (minkowskiDiff_mono subset_rfl
    (Metric.closedBall_subset_closedBall herr.le)) ?_
  exact sys.timeIntervalStepInner_inner hr η hside X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
