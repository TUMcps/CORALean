module

public import CORALean.ContDynamics.LinearSys.Theorems.ExistsTimePointStepErrorLt
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepInnerInner
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono

@[expose] public section

/-!
# An inner approximation at a tolerance the caller names

`exists_timePointStepError_lt` composed with `timePointStepInner_inner`: for every `ε > 0` there is
a step at which taking off the ball of radius `ε`, the caller's own tolerance, already yields an
inner approximation. That is what makes the guarantee usable: `timePointStepError` mentions a matrix
norm and an exponential remainder, so an implementation that had to evaluate it to know what to
subtract would be subtracting a number it cannot certify. Here the step is chosen to put the true
error under the tolerance, and `minkowskiDiff_mono` does the rest. The other direction does not
compose: "the inner approximation fills the exact set to within `ε`" is false however small `ε` is,
since where the exact set is lower dimensional every Minkowski difference by a ball is empty.

## Inputs
* `sys` – linear system
* `X₀` – initial zonotope
* `U` – input zonotope
* `η` – Taylor order
* `ε` – admissible error

## Hypotheses
* `hε` – error positive

## Conclusion
* some step is short enough that its enclosure minus the error ball lies inside what it reaches
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

/-- Some step is short enough that the enclosure minus a ball of the caller's
own radius `ε` is already inside what the step reaches. -/
theorem LinearSys.exists_timePointStepInner_inner (sys : LinearSys 𝕋 n)
    (X₀ U : Zonotope (Vec ℝ n)) (η : ℕ) {ε : ℝ} (hε : 0 < ε) : -- --- CONCL ---
    ∃ r : ℝ, 0 < r ∧ sys.timePointStepError r η U < ε ∧
      minkowskiDiff (sys.timePointStep (S := 𝒵) r η X₀ U).construct
          (Metric.closedBall (0 : Vec ℝ n) ε)
        ⊆ (fun x₀ => exp (r • toRealMat sys.A) *ᵥ x₀) '' X₀.construct
          + sys.inputReach (S := 𝒵) U r := by -- --- PROOF ---
  obtain ⟨r, hr, herr, hside⟩ := sys.exists_timePointStepError_lt U η hε
  refine ⟨r, hr, herr, ?_⟩
  -- the true error is under the tolerance, so its ball is inside the one taken off
  refine subset_trans (minkowskiDiff_mono subset_rfl
    (Metric.closedBall_subset_closedBall herr.le)) ?_
  exact sys.timePointStepInner_inner hr η hside X₀ U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
