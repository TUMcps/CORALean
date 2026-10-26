module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Specification.STL.Definitions.TreeHasAllTimes
public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeToReal
public import CORALean.Specification.STL.Theorems.TreeMaximumTimeFromAdd

@[expose] public section

/-!
# `maximumTimeFloat` bounds the exact `maximumTime` from above

`maximumTimeFloat` rounds every sum of times up and takes the larger of two times exactly, so for a
tree whose time bounds denote nonnegative reals its value is at least the exact latest time of the
tree read as reals.

## Inputs
* `φ` – formula

## Hypotheses
* `hφ` – every time bound denotes a nonnegative real

## Conclusion
* the exact `maximumTime` of the reading is at most the float one, read as a real
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

private theorem aux_maximumTimeFromFloat_outer (φ : STL.Tree 𝕋 𝕋 n)
    (hφ : φ.HasAllTimes (fun a => 0 ≤ SoundFloatArithmetic.toReal a)) (t : 𝕋)
    (ht : 0 ≤ SoundFloatArithmetic.toReal t) : -- --- CONCL ---
    ((φ.toReal.maximumTimeFrom (Real.toNNReal (SoundFloatArithmetic.toReal t)) : ℝ≥0) : ℝ) ≤
      SoundFloatArithmetic.toReal (φ.maximumTimeFromFloat t) := by -- --- PROOF ---
  -- induction on the formula, one case per node
  induction φ generalizing t with
  | tt => simp [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
    STL.Tree.maximumTimeFromFloat, ht]
  | ff => simp [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
    STL.Tree.maximumTimeFromFloat, ht]
  | cmp op e₁ e₂ => simp [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
    STL.Tree.maximumTimeFromFloat, ht]
  | not φ ih => exact ih hφ t ht
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
      STL.Tree.maximumTimeFromFloat, NNReal.coe_max, toReal_maximum]
    exact max_le_max (ihφ hφ.1 t ht) (ihψ hφ.2 t ht)
  -- the remaining cases
  | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
      STL.Tree.maximumTimeFromFloat, NNReal.coe_max, toReal_maximum]
    exact max_le_max (ihφ hφ.1 t ht) (ihψ hφ.2 t ht)
  | next a φ ih =>
    have ha := hφ.1
    have ht2 : 0 ≤ SoundFloatArithmetic.toReal (addUp a t) := by
      have := add_le_addUp a t; linarith
    have key := ih hφ.2 (addUp a t) ht2
    have hsum : Real.toNNReal (SoundFloatArithmetic.toReal a) + Real.toNNReal
      (SoundFloatArithmetic.toReal t) ≤
        Real.toNNReal (SoundFloatArithmetic.toReal (addUp a t)) := by
      rw [← Real.toNNReal_add ha ht]
      exact Real.toNNReal_le_toNNReal (add_le_addUp a t)
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
      STL.Tree.maximumTimeFromFloat] at key ⊢
    rw [STL.Tree.maximumTimeFrom_eq_add] at key ⊢
    refine le_trans ?_ key
    exact_mod_cast add_le_add hsum le_rfl
  -- the remaining cases
  | «finally» a b φ ih =>
    have hb := hφ.2.1
    have := ih hφ.2.2 t ht
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
      STL.Tree.maximumTimeFromFloat,
      NNReal.coe_add, Real.coe_toNNReal _ hb] at this ⊢
    exact le_trans (add_le_add_right this _) (add_le_addUp b _)
  | globally a b φ ih =>
    have hb := hφ.2.1
    have := ih hφ.2.2 t ht
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
      STL.Tree.maximumTimeFromFloat,
      NNReal.coe_add, Real.coe_toNNReal _ hb] at this ⊢
    exact le_trans (add_le_add_right this _) (add_le_addUp b _)
  -- the remaining cases
  | «until» a b φ ψ ihφ ihψ =>
    have hb := hφ.2.1
    have h1 := ihφ hφ.2.2.1 t ht
    have h2 := ihψ hφ.2.2.2 t ht
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
      STL.Tree.maximumTimeFromFloat,
      NNReal.coe_add, NNReal.coe_max, Real.coe_toNNReal _ hb] at h1 h2 ⊢
    refine le_trans (add_le_add_right (max_le_max h1 h2) _) ?_
    rw [← toReal_maximum]
    exact add_le_addUp b _
  | release a b φ ψ ihφ ihψ =>
    have hb := hφ.2.1
    have h1 := ihφ hφ.2.2.1 t ht
    have h2 := ihψ hφ.2.2.2 t ht
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.maximumTimeFrom,
      STL.Tree.maximumTimeFromFloat,
      NNReal.coe_add, NNReal.coe_max, Real.coe_toNNReal _ hb] at h1 h2 ⊢
    refine le_trans (add_le_add_right (max_le_max h1 h2) _) ?_
    rw [← toReal_maximum]
    exact add_le_addUp b _


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.maximumTimeFloat_outer (φ : STL.Tree 𝕋 𝕋 n)
    (hφ : φ.HasAllTimes (fun a => 0 ≤ SoundFloatArithmetic.toReal a)) :
    (φ.toReal.maximumTime : ℝ) ≤ SoundFloatArithmetic.toReal φ.maximumTimeFloat := by
  have := aux_maximumTimeFromFloat_outer φ hφ FloatOps.zero (by simp [toReal_zero])
  simpa [STL.Tree.maximumTime, STL.Tree.maximumTimeFloat, toReal_zero] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
