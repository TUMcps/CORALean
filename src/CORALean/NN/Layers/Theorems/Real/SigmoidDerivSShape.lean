import CORALean.NN.Layers.Definitions.SShape
import CORALean.NN.Layers.Definitions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The logistic function is S-shaped

Its derivative `σ(t) σ(-t) = 1 / (2 + 2 cosh t)` is even and non-increasing in `|t|`, so
`sShapeDerBounds_sound` applies to it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `sigmoidDeriv` is even and non-increasing on `[0, ∞)`. -/
theorem sigmoidDeriv_sShape : SShape sigmoidDeriv where
  even t := by
    show sigmoid (-t) * sigmoid (-(-t)) = sigmoid t * sigmoid (-t)
    rw [neg_neg, mul_comm]
  anti {s t} hs hst := by
    -- the derivative is `(2 + 2 cosh t)⁻¹`
    have key : ∀ x : ℝ, sigmoidDeriv x = (2 + 2 * Real.cosh x)⁻¹ := fun x => by
      show (1 + Real.exp (-x))⁻¹ * (1 + Real.exp (-(-x)))⁻¹ = _
      rw [neg_neg, ← mul_inv, Real.cosh_eq]
      congr 1
      have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    rw [key, key]
    have hc : Real.cosh s ≤ Real.cosh t :=
      Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hs, abs_of_nonneg (hs.trans hst)]; exact hst)
    have hpos : 0 < 2 + 2 * Real.cosh s := by positivity
    exact inv_anti₀ hpos (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
