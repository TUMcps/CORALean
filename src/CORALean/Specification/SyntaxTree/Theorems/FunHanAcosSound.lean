module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains

@[expose] public section

/-!
# `aaux_cos_` is sound

`aaux_cos_` keeps every solution of `acos s ∈ int`, for a target inside the range of `acos`.

## Inputs
* `prev` – previous interval

## Hypotheses
* `hd₁` – the interval stays above minus one
* `hd₂` – the interval stays below one

## Conclusion
* the inverse of the inverse cosine keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aaux_cos_` is sound for `acos` on an operand inside `[-1,1]`. -/
theorem SyntaxTree.funHanAcos_sound (prev : Dom) (hd₁ : -1 ≤ prev.inf 0)
    (hd₂ : prev.sup 0 ≤ 1) : -- --- CONCL ---
    IsUnarySound Unary.acos.fn prev (Real.Interval.acos prev) funHanAcos := by -- --- PROOF ---
  intro int hw s hs hi
  have h : int.inf 0 ≤ Real.arccos s ∧ Real.arccos s ≤ int.sup 0 := hi
  have hs1 : -1 ≤ s := hd₁.trans hs.1
  have hs2 : s ≤ 1 := hs.2.trans hd₂
  have e : Real.cos (Real.arccos s) = s := Real.cos_arccos hs1 hs2
  have hlo : 0 ≤ int.inf 0 := (Real.arccos_nonneg _).trans hw.1
  have hsup : int.sup 0 ≤ Real.pi := hw.2.trans (Real.arccos_le_pi _)
  have hnd : ¬ int.sup 0 < 0 := not_lt.2 (hlo.trans (h.1.trans h.2))
  unfold funHanAcos
  simp only [not_lt.2 hlo, hnd, if_false]
  have l₁ : Real.cos (int.sup 0) ≤ s := by
    rw [← e]; exact Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _) hsup h.2
  have l₂ : s ≤ Real.cos (int.inf 0) := by
    rw [← e]; exact Real.cos_le_cos_of_nonneg_of_le_pi hlo (Real.arccos_le_pi _) h.1
  obtain ⟨m₁, m₂⟩ := meet_contains hs ((min_le_right _ _).trans l₁) (l₂.trans (le_max_left _ _))
  exact ⟨_, rfl, m₁, m₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
