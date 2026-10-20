module

public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import Mathlib.Analysis.Normed.Ring.Lemmas

@[expose] public section

/-!
# `plus` adds the two sup-norm ball radii

The triangle inequality, carried through `plus_exact`: a Minkowski sum of two
balls sits inside the ball of the summed radius, and `Z₁.plus Z₂` denotes
exactly that sum.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope
* `r₁` – first radius
* `r₂` – second radius

## Hypotheses
* `h₁` – `Z₁` lies in its ball
* `h₂` – `Z₂` lies in its ball

## Conclusion
* the sum lies in the ball of the summed radii
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Z₁.plus Z₂` reaches no further than `r₁ + r₂` once each summand reaches no
further than its own radius. -/
theorem Zonotope.plus_subset_closedBall {Z₁ Z₂ : Zonotope (Vec ℝ n)} {r₁ r₂ : ℝ}
    (h₁ : Z₁.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r₁)
    (h₂ : Z₂.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r₂) : -- --- CONCL ---
    (Z₁.plus Z₂).construct ⊆ Metric.closedBall (0 : Vec ℝ n) (r₁ + r₂) := by -- --- PROOF ---
  rw [← Zonotope.plus_exact]
  rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  have h1 := h₁ hx₁
  have h2 := h₂ hx₂
  rw [Metric.mem_closedBall, dist_zero_right] at h1 h2
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖x₁ + x₂‖ ≤ ‖x₁‖ + ‖x₂‖ := norm_add_le _ _
    _ ≤ r₁ + r₂ := add_le_add h1 h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
