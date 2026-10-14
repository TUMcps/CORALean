module

public import CORALean.ContSet.Interval.Real.Operations.Acosh
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `aaux_cosh_` is sound

`aaux_cosh_` keeps every solution of `acosh s ∈ int` for `s ≥ 1`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `cosh` is monotone on the nonnegative numbers. -/
private theorem SyntaxTree.cosh_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.cosh a ≤ Real.cosh b := by
  rw [Real.cosh_le_cosh, abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]
  exact hab

/-- `aaux_cosh_` is sound for `acosh` on an operand `≥ 1`. -/
theorem SyntaxTree.funHanAcosh_sound (prev : Dom) (hd : 1 ≤ prev.inf 0) :
    UnarySound Unary.acosh.fn prev (Real.Interval.acosh prev) funHanAcosh := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.arcosh s ∧ Real.arcosh s ≤ int.sup 0 := hi
  have hs1 : 1 ≤ s := hd.trans hs.1
  have h0 : 0 ≤ Real.arcosh s := Real.arcosh_nonneg hs1
  have hnd : ¬ int.sup 0 < 0 := not_lt.2 (h0.trans h.2)
  have e : Real.cosh (Real.arcosh s) = s := Real.cosh_arcosh hs1
  have l₂ : s ≤ Real.cosh (int.sup 0) := by
    rw [← e]; exact cosh_mono_nonneg h0 h.2
  unfold funHanAcosh
  by_cases hl : int.inf 0 < 0
  · simp only [hl, hnd, if_true, if_false, interval]
    have l₁ : Real.cosh 0 ≤ s := by
      rw [← e]; exact cosh_mono_nonneg le_rfl h0
    obtain ⟨m₁, m₂⟩ := meet_contains hs ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
    exact ⟨_, rfl, m₁, m₂⟩
  -- unfold the definitions
  · simp only [hl, hnd, if_false]
    have l₁ : Real.cosh (int.inf 0) ≤ s := by
      rw [← e]; exact cosh_mono_nonneg (not_lt.1 hl) h.1
    obtain ⟨m₁, m₂⟩ := meet_contains hs ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
    exact ⟨_, rfl, m₁, m₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
