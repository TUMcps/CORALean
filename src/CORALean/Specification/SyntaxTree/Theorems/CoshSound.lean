module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.Specification.SyntaxTree.Definitions.IsUnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.AuxSignedSpec
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `aux_cosh_` is sound

`aux_cosh_` keeps every solution of `cosh s ∈ int`, with the sign `intPrev` allows.

## Inputs
* `prev` – previous interval

## Hypotheses
* none

## Conclusion
* the inverse of cosh keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_cosh_` is sound for `cosh`. -/
theorem SyntaxTree.cosh_sound (prev : Dom) : -- --- CONCL ---
    IsUnarySound Unary.cosh.fn prev (Real.Interval.cosh prev) funHanCosh := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.cosh s ∧ Real.cosh s ≤ int.sup 0 := hi
  have hc1 : 1 ≤ Real.cosh s := Real.one_le_cosh s
  have hnd : ¬ int.sup 0 < 1 := not_lt.2 (hc1.trans h.2)
  have hr : Real.arcosh (Real.cosh s) = |s| := by
    rw [← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg s)]
  have l₂ : |s| ≤ Real.arcosh (int.sup 0) := by
    rw [← hr]; exact (Real.arcosh_le_arcosh (by linarith) (by linarith)).2 h.2
  unfold funHanCosh
  by_cases hl : int.inf 0 < 1
  · simp only [hl, hnd, if_true, if_false, interval]
    have l₁ : Real.arcosh 1 ≤ |s| := by
      rw [← hr]; exact (Real.arcosh_le_arcosh one_pos (by linarith)).2 hc1
    obtain ⟨lo, hi', e, c₁, c₂⟩ := signedRoots_spec hs l₁ l₂
    obtain ⟨m₁, m₂⟩ := meet_contains hs c₁ c₂
    exact ⟨_, by rw [e], m₁, m₂⟩
  -- unfold the definitions
  · simp only [hl, hnd, if_false]
    have l₁ : Real.arcosh (int.inf 0) ≤ |s| := by
      rw [← hr]; exact (Real.arcosh_le_arcosh (by linarith [not_lt.1 hl]) (by linarith)).2 h.1
    obtain ⟨lo, hi', e, c₁, c₂⟩ := signedRoots_spec hs l₁ l₂
    obtain ⟨m₁, m₂⟩ := meet_contains hs c₁ c₂
    exact ⟨_, by rw [e], m₁, m₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
