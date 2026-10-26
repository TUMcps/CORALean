module

public import CORALean.Specification.STL.Operations.TreeCombineNextFloat
public import CORALean.Specification.STL.Operations.TreeToReal
public import CORALean.Specification.STL.Theorems.TreeSatCombineNext

@[expose] public section

/-!
# `combineNextFloat` read as reals

For every float formula, `combineNextFloat` read as reals holds of the same traces as `combineNext`
of the formula read as reals: nested `next` are merged only where the stored sum is exact and both
bounds are nonnegative, and stay nested otherwise.

## Inputs
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the two formulas hold of the same traces
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

/-- The test of `combineNextFloat` certifies a nonnegative, exact sum. -/
private theorem aux_exact (a b : 𝕋)
    (h : (le zero a && le zero b && le (addUp a b) (addDown a b)) = true) : -- --- CONCL ---
    0 ≤ toReal a ∧ 0 ≤ toReal b ∧ toReal (addUp a b) = toReal a + toReal b := by -- --- PROOF ---
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have ha := toReal_le_of_le h1
  have hb := toReal_le_of_le h2
  have hc := toReal_le_of_le h3
  have := add_le_addUp a b
  have := addDown_le_add a b
  rw [toReal_zero] at ha hb
  exact ⟨ha, hb, le_antisymm (by linarith) (by linarith)⟩

/-- `combineNextFloat` read as reals keeps the traces the formula holds of. -/
private theorem aux_sat (φ : STL.Tree 𝕋 𝕋 n) (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    φ.combineNextFloat.toReal.Satisfies ξ ↔ φ.toReal.Satisfies ξ := by -- --- PROOF ---
  -- follow the recursion of `combineNextFloat`, one case per node
  induction φ using STL.Tree.combineNextFloat.induct generalizing ξ with
  | case1 a φ ψ h ihφ ihψ =>
    simp only [STL.Tree.combineNextFloat, h, ↓reduceIte, STL.Tree.toReal, STL.Tree.map,
      STL.Tree.Satisfies] at ihφ ihψ ⊢
    rw [ihφ ξ, ihψ ξ]
  | case2 a φ ψ h => simp [STL.Tree.combineNextFloat, h]
  | case3 a φ ψ h ihφ ihψ =>
    simp only [STL.Tree.combineNextFloat, h, ↓reduceIte, STL.Tree.toReal, STL.Tree.map,
      STL.Tree.Satisfies] at ihφ ihψ ⊢
    rw [ihφ ξ, ihψ ξ]
  | case4 a φ ψ h => simp [STL.Tree.combineNextFloat, h]
  | case5 a φ ih =>
    simp only [STL.Tree.combineNextFloat, STL.Tree.toReal, STL.Tree.map,
      STL.Tree.Satisfies] at ih ⊢
    rw [ih ξ]
  -- two nested `next`: merged only where the stored sum is exact
  | case6 a b φ h ih =>
    obtain ⟨ha, hb, hs⟩ := aux_exact a b h
    rw [STL.Tree.combineNextFloat, if_pos h, ih ξ]
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.Satisfies]
    rw [Time.shift_shift, hs, Real.toNNReal_add ha hb, add_comm]
  | case7 a b φ h ih =>
    rw [STL.Tree.combineNextFloat, if_neg h]
    have := ih (Time.shift ξ (Real.toNNReal (toReal a)))
    simp only [STL.Tree.toReal, STL.Tree.map, STL.Tree.Satisfies] at this ⊢
    exact this
  -- the merged and the kept `next`, then the connectives
  | case8 a φ h₁ h₂ h₃ h₄ => rw [STL.Tree.combineNextFloat] <;> first | rfl | assumption
  | case9 φ ψ ihφ ihψ =>
    simp only [STL.Tree.combineNextFloat, STL.Tree.toReal, STL.Tree.map,
      STL.Tree.Satisfies] at ihφ ihψ ⊢
    rw [ihφ ξ, ihψ ξ]
  | case10 φ ψ ihφ ihψ =>
    simp only [STL.Tree.combineNextFloat, STL.Tree.toReal, STL.Tree.map,
      STL.Tree.Satisfies] at ihφ ihψ ⊢
    rw [ihφ ξ, ihψ ξ]
  | case11 φ ih =>
    simp only [STL.Tree.combineNextFloat, STL.Tree.toReal, STL.Tree.map,
      STL.Tree.Satisfies] at ih ⊢
    rw [ih ξ]
  | case12 φ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ =>
    rw [STL.Tree.combineNextFloat] <;> first | rfl | assumption


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.combineNextFloat_toReal (φ : STL.Tree 𝕋 𝕋 n) (ξ : ℝ≥0 → Fin n → ℝ) :
    φ.combineNextFloat.toReal.Satisfies ξ ↔ φ.toReal.combineNext.Satisfies ξ :=
  (aux_sat φ ξ).trans (STL.Tree.sat_combineNext φ.toReal ξ).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
