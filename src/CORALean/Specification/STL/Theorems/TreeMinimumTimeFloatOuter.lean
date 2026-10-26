module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeToReal
public import CORALean.Specification.STL.Theorems.TreeMinimumTimeFromAdd

@[expose] public section

/-!
# `minimumTimeFloat` bounds the exact `minimumTime` from below

`minimumTimeFloat` rounds every sum of times down and takes the smaller of two times exactly, so its
value is at most the exact earliest time of the tree read as reals.

## Inputs
* `φ` – formula

## Hypotheses
* none

## Conclusion
* the float `minimumTime`, read as a real, is at most the exact one of the reading
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic
open scoped NNReal

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_minimumTimeFromFloat_outer (φ : STL.Tree 𝕋 𝕋 n) (t : 𝕋) : -- --- CONCL ---
    toReal (φ.minimumTimeFromFloat t) ≤
      ((φ.toReal.minimumTimeFrom (Real.toNNReal (toReal t)) : ℝ≥0) : ℝ) := by -- --- PROOF ---
  -- the rounded-down sum stays below the exact one; then induction on the formula
  have hnn : ∀ x : ℝ, x ≤ (Real.toNNReal x : ℝ) := fun x => Real.le_coe_toNNReal x
  have hsum : ∀ a t : 𝕋, SoundFloatArithmetic.toReal (addDown a t) ≤
      (Real.toNNReal (SoundFloatArithmetic.toReal a) + Real.toNNReal (SoundFloatArithmetic.toReal
        t) : ℝ≥0) := by
    intro a t
    refine (addDown_le_add a t).trans ?_
    push_cast
    exact add_le_add (hnn _) (hnn _)
  induction φ generalizing t with
  | tt => exact hnn _
  | ff => exact hnn _
  | cmp op e₁ e₂ => exact hnn _
  -- the remaining cases
  | not φ ih => exact ih t
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.minimumTimeFrom,
      STL.Tree.minimumTimeFromFloat,
      NNReal.coe_min, toReal_minimum]
    exact min_le_min (ihφ t) (ihψ t)
  | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.minimumTimeFrom,
      STL.Tree.minimumTimeFromFloat,
      NNReal.coe_min, toReal_minimum]
    exact min_le_min (ihφ t) (ihψ t)
  -- the shift is rounded down, so the sum stays below the exact one
  | next a φ ih =>
    have key := ih (addDown a t)
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.minimumTimeFrom,
      STL.Tree.minimumTimeFromFloat] at key ⊢
    refine le_trans key ?_
    rw [STL.Tree.minimumTimeFrom_eq_add _ (Real.toNNReal (SoundFloatArithmetic.toReal (addDown a
      t))),
      STL.Tree.minimumTimeFrom_eq_add _ (Real.toNNReal (SoundFloatArithmetic.toReal a) +
        Real.toNNReal (SoundFloatArithmetic.toReal t))]
    have h : Real.toNNReal (SoundFloatArithmetic.toReal (addDown a t)) ≤
        Real.toNNReal (SoundFloatArithmetic.toReal a) + Real.toNNReal
          (SoundFloatArithmetic.toReal t) := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact_mod_cast hsum a t
    exact_mod_cast add_le_add h le_rfl
  -- the remaining cases
  | «finally» a b φ ih =>
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.minimumTimeFrom,
      STL.Tree.minimumTimeFromFloat,
      NNReal.coe_add]
    exact hsum a t
  | globally a b φ ih =>
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.minimumTimeFrom,
      STL.Tree.minimumTimeFromFloat,
      NNReal.coe_add]
    exact hsum a t
  | «until» a b φ ψ ihφ ihψ => exact hnn _
  | release a b φ ψ ihφ ihψ => exact hnn _


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.minimumTimeFloat_outer (φ : STL.Tree 𝕋 𝕋 n) :
    SoundFloatArithmetic.toReal φ.minimumTimeFloat ≤ (φ.toReal.minimumTime : ℝ) := by
  have := aux_minimumTimeFromFloat_outer φ FloatOps.zero
  simpa [STL.Tree.minimumTime, STL.Tree.minimumTimeFloat, toReal_zero] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
