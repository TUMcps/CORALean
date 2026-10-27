module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.ShiftShift
public import CORALean.Specification.STL.Theorems.ShiftZero

@[expose] public section

/-!
# Rewriting, `U[0,j]`

[1, Table 1] `φ₁ U[0,j] φ₂ ⇐ φ₂ ∨ (φ₁ ∧ G_I φ₁ ∧ (F_I φ₂ ∨ X₁(φ₁ U[0,j-1] φ₂)))` for `1 ≤ j`.

The window is `I = (0,1)`, as the table assumes `c = 1`, and the bounds `i`, `j` are natural numbers
with the side condition the subtraction needs.

## Inputs
* `φ₁` – left formula
* `φ₂` – right formula
* `j` – interval upper bound
* `ξ` – trace

## Hypotheses
* `hj` – the bound is positive
* `h` – the rewritten formula holds

## Conclusion
* the until from zero holds

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.rewrite_until_zero (φ₁ φ₂ : STL.Formula X) (j : ℕ) (hj : 1 ≤ j) (ξ : ℝ≥0 → X)
    (h : (φ₂.or (φ₁.and ((STL.Formula.globOpen 1 φ₁).and
      ((STL.Formula.finOpen 1 φ₂).or
        (STL.Formula.next 1 (STL.Formula.until 0 ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))))).Satisfies ξ)
    : -- --- CONCL ---
    (STL.Formula.until 0 (j : ℝ≥0) φ₁ φ₂).Satisfies ξ := by -- --- PROOF ---
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.Satisfies, Time.shift_shift,
    Nat.add_sub_cancel] at h ⊢
  rcases h with h | ⟨h₁, h₂, h₃⟩
  · refine ⟨0, le_rfl, zero_le, ?_, fun t ht => absurd ht (not_lt_zero)⟩
    rwa [Time.shift_zero]
  rcases h₃ with ⟨s, hs₀, hs₁, hs₂⟩ | ⟨t, ht₁, ht₂, ht₃, ht₄⟩
  · -- `F_I φ₂` holds at some `s < 1`, with `φ₁` before it by `G_I φ₁`
    refine ⟨s, zero_le, ?_, by simpa using hs₂, fun t ht => ?_⟩
    · push_cast; exact (hs₁.trans_le (by simp)).le
    · rcases eq_zero_or_pos t with rfl | ht0
      · rwa [Time.shift_zero]
      · exact h₂ t ht0 (ht.trans hs₁)
  · -- the until holds one step later, at `t + 1`
    refine ⟨t + 1, zero_le, ?_, ?_, ?_⟩
    · push_cast; exact add_le_add ht₂ le_rfl
    · exact ht₃
    · intro s hs
      rcases lt_or_ge s 1 with hs1 | hs1
      · rcases eq_zero_or_pos s with rfl | hs0
        · rw [Time.shift_zero]; exact h₁
        · exact h₂ s hs0 hs1
      · obtain ⟨d, rfl⟩ := exists_add_of_le hs1
        rw [add_comm] at hs
        exact (by rw [add_comm]; exact ht₄ d (lt_of_add_lt_add_right hs))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
