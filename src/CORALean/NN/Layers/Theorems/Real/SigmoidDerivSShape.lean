module

public import CORALean.NN.Layers.Definitions.SShape
public import CORALean.NN.Layers.Definitions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

/-!
# The logistic function is S-shaped

Its derivative `σ(t) σ(-t) = 1 / (2 + 2 cosh t)` is even and non-increasing in `|t|`, so
`sShapeDerBounds_sound` applies to it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `sigmoidDeriv_sShape` below needs these
/-- The denominator `2 + 2 cosh t` of the logistic derivative. -/
noncomputable def aux_derivDenom (t : ℝ) : ℝ := 2 + 2 * Real.cosh t

theorem aux_derivDenom_pos (t : ℝ) : 0 < aux_derivDenom t := by
  unfold aux_derivDenom
  positivity

theorem aux_derivDenom_neg (t : ℝ) : aux_derivDenom (-t) = aux_derivDenom t := by
  unfold aux_derivDenom
  rw [Real.cosh_neg]

theorem aux_derivDenom_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    aux_derivDenom s ≤ aux_derivDenom t := by
  have hc : Real.cosh s ≤ Real.cosh t :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hs, abs_of_nonneg (hs.trans hst)]; exact hst)
  unfold aux_derivDenom
  linarith

theorem aux_sigmoidDeriv_eq (t : ℝ) : sigmoidDeriv t = (aux_derivDenom t)⁻¹ := by -- --- PROOF ---
  show (1 + Real.exp (-t))⁻¹ * (1 + Real.exp (-(-t)))⁻¹ = _
  rw [neg_neg, ← mul_inv, aux_derivDenom, Real.cosh_eq]
  congr 1
  have : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- `sigmoidDeriv` is even and non-increasing on `[0, ∞)`. -/
theorem sigmoidDeriv_sShape : SShape sigmoidDeriv where
  even t := by rw [aux_sigmoidDeriv_eq, aux_sigmoidDeriv_eq, aux_derivDenom_neg]
  anti {s t} hs hst := by
    rw [aux_sigmoidDeriv_eq, aux_sigmoidDeriv_eq]
    exact inv_anti₀ (aux_derivDenom_pos s) (aux_derivDenom_mono hs hst)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
