module

public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# `mtimes` scales the sup-norm ball by the operator norm

The plain-matrix counterpart to `mtimesIntervalMat_subset_closedBall`: there
the bound is an entrywise one against the operand's `ℓ¹` reach, because an
interval matrix has no single matrix to appeal to; here `M` is one matrix, so
the ordinary operator-norm inequality `‖M *ᵥ x‖ ≤ ‖M‖ * ‖x‖` carries the ball
straight through, at the `l∞` operator norm `Vec ℝ n`'s own sup norm already
pairs with.

## Inputs
* `M` – matrix
* `Z` – zonotope
* `r` – ball radius

## Hypotheses
* `h` – `Z` lies in the ball

## Conclusion
* the image lies in the ball scaled by the norm of `M`
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mtimes M Z` reaches no further than `‖M‖ * r` once `Z` reaches no further
than `r`: the image of a ball under `M` sits inside the ball scaled by `M`'s
operator norm. -/
theorem Zonotope.mtimes_subset_closedBall (M : Mat ℝ m n) {Z : Zonotope (Vec ℝ n)} {r : ℝ}
    (h : Z.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r) : -- --- CONCL ---
    (Zonotope.mtimes M Z).construct
      ⊆ Metric.closedBall (0 : Vec ℝ m) (‖M‖ * r) := by -- --- PROOF ---
  rw [← Zonotope.mtimes_exact]
  rintro _ ⟨x, hx, rfl⟩
  have hxr := h hx
  rw [Metric.mem_closedBall, dist_zero_right] at hxr
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖M *ᵥ x‖ ≤ ‖M‖ * ‖x‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ ‖M‖ * r := mul_le_mul_of_nonneg_left hxr (norm_nonneg _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
