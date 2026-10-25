module

public import CORALean.ContSet.Interval.Real.Operations.Sqrt
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `aux_sqrt_` is sound

`aux_sqrt_` keeps every solution of `sqrt s ∈ int` with `s ≥ 0`.

## Inputs
* `prev` – previous interval

## Hypotheses
* `hd` – the interval is nonnegative

## Conclusion
* the inverse of the square root keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_sqrt_` is sound for `sqrt` on a nonnegative operand. -/
theorem SyntaxTree.sqrt_sound (prev : Dom) (hd : 0 ≤ prev.inf 0) : -- --- CONCL ---
    IsUnarySound Unary.sqrt.fn prev (Real.Interval.sqrt prev) funHanSqrt := by -- --- PROOF ---
  intro int _ s hs hi
  have hs0 : 0 ≤ s := hd.trans hs.1
  have h : int.inf 0 ≤ Real.sqrt s ∧ Real.sqrt s ≤ int.sup 0 := hi
  have e : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
  have hnd : ¬ int.sup 0 < 0 := not_lt.2 ((Real.sqrt_nonneg s).trans h.2)
  have l₂ : s ≤ int.sup 0 ^ 2 := by
    rw [← e]; exact pow_le_pow_left₀ (Real.sqrt_nonneg s) h.2 2
  unfold funHanSqrt
  by_cases hl : int.inf 0 < 0
  · simp only [hl, hnd, if_true, if_false, interval]
    obtain ⟨h₁, h₂⟩ := meet_contains hs (lo := min ((0 : ℝ) ^ 2) (int.sup 0 ^ 2))
      (hi := max ((0 : ℝ) ^ 2) (int.sup 0 ^ 2)) ((min_le_left _ _).trans (by simpa using hs0))
      (l₂.trans (le_max_right _ _))
    exact ⟨_, rfl, h₁, h₂⟩
  -- the fact `int.inf 0 ^ 2 ≤ s`
  · have l₁ : int.inf 0 ^ 2 ≤ s := by
      rw [← e]; exact pow_le_pow_left₀ (not_lt.1 hl) h.1 2
    simp only [hl, hnd, if_false]
    obtain ⟨h₁, h₂⟩ := meet_contains hs (lo := min (int.inf 0 ^ 2) (int.sup 0 ^ 2))
      (hi := max (int.inf 0 ^ 2) (int.sup 0 ^ 2)) ((min_le_left _ _).trans l₁)
      (l₂.trans (le_max_right _ _))
    exact ⟨_, rfl, h₁, h₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
