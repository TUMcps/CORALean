module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains

@[expose] public section

/-!
# `aaux_sin_` is sound

`aaux_sin_` keeps every solution of `asin s ∈ int`, for a target inside the range of `asin`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aaux_sin_` is sound for `asin` on an operand inside `[-1,1]`. -/
theorem SyntaxTree.funHanAsin_sound (prev : Dom) (hd₁ : -1 ≤ prev.inf 0) (hd₂ : prev.sup 0 ≤ 1) :
    UnarySound Unary.asin.fn prev (Real.Interval.asin prev) funHanAsin := by -- --- PROOF ---
  intro int hw s hs hi
  have h : int.inf 0 ≤ Real.arcsin s ∧ Real.arcsin s ≤ int.sup 0 := hi
  have hs1 : -1 ≤ s := hd₁.trans hs.1
  have hs2 : s ≤ 1 := hs.2.trans hd₂
  have e : Real.sin (Real.arcsin s) = s := Real.sin_arcsin hs1 hs2
  have hsup : int.sup 0 ≤ Real.pi / 2 :=
    hw.2.trans (Real.arcsin_le_pi_div_two _)
  have hnd : ¬ int.sup 0 < -(Real.pi / 2) :=
    not_lt.2 ((Real.neg_pi_div_two_le_arcsin s).trans h.2)
  unfold funHanAsin
  by_cases hl : int.inf 0 < -(Real.pi / 2)
  · -- the target is cut to `[-pi/2, pi/2]`
    simp only [hl, hnd, if_true, if_false, interval]
    have l₁ : Real.sin (-(Real.pi / 2)) ≤ s := by
      rw [Real.sin_neg, Real.sin_pi_div_two]; exact hs1
    have l₂ : s ≤ Real.sin (Real.pi / 2) := by rw [Real.sin_pi_div_two]; exact hs2
    obtain ⟨m₁, m₂⟩ := meet_contains hs ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
    exact ⟨_, rfl, m₁, m₂⟩
  · simp only [hl, hnd, if_false]
    have hlo : -(Real.pi / 2) ≤ int.inf 0 := not_lt.1 hl
    have l₁ : Real.sin (int.inf 0) ≤ s := by
      rw [← e]; exact Real.sin_le_sin_of_le_of_le_pi_div_two hlo (Real.arcsin_le_pi_div_two _) h.1
    have l₂ : s ≤ Real.sin (int.sup 0) := by
      rw [← e]; exact Real.sin_le_sin_of_le_of_le_pi_div_two (Real.neg_pi_div_two_le_arcsin _) hsup
          h.2
    obtain ⟨m₁, m₂⟩ := meet_contains hs ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
    exact ⟨_, rfl, m₁, m₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
