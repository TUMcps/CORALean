module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The Cauchy-Schwarz bound of the diagonal direction

For two reals `s₁`, `s₂` the inner product with the unit diagonal `(1, 1)/√2` is at most the
Euclidean norm: `(s₁ + s₂)/√2 ≤ ‖(s₁, s₂)‖₂`. The norm is written as `√(s₁² + s₂²)` since `Vec`
carries the supremum norm.

## Inputs
* `s₁` – first coordinate
* `s₂` – second coordinate

## Hypotheses
* none

## Conclusion
* the diagonal component is at most the Euclidean norm
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `(s₁ + s₂)/√2 ≤ ‖s‖₂`. -/
theorem add_div_sqrt_two_le_sqrt (s₁ s₂ : ℝ) :
    (s₁ + s₂) / √2 ≤ √(s₁ ^ 2 + s₂ ^ 2) := by
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr two_pos
  rw [div_le_iff₀ h2, ← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (s₁ - s₂)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
