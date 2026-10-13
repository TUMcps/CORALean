import Mathlib.Analysis.Complex.Exponential

/-!
# The logistic function, and its derivative

CORA's `nnSigmoidLayer` applies the logistic function, defined here because Mathlib has none
and stated as `(1 + e⁻ᵗ)⁻¹` so that monotonicity is the denominator's. The derivative is
written `σ t · σ (-t)` rather than `σ t (1 - σ t)`: each factor is then monotone in `t` on its
own, so the ends of a box bracket the product with no case on where zero lies. What the
sigmoid layer encloses, over ℝ, and never what it runs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def sigmoid (t : ℝ) : ℝ := (1 + Real.exp (-t))⁻¹

noncomputable def sigmoidDeriv (t : ℝ) : ℝ := sigmoid t * sigmoid (-t)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
