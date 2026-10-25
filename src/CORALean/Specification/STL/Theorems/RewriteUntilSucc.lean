module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.ShiftShift
public import CORALean.Specification.STL.Theorems.ShiftZero

@[expose] public section

/-!
# Rewriting, `U[i,j]` past `1`

[1, Table 1] `φ₁ U[i,j] φ₂ ⇐ φ₁ ∧ G_I φ₁ ∧ X₁(φ₁ U[i-1,j-1] φ₂)` for `I = (0,1)` and `1 ≤ i ≤ j`.

The window is `I = (0,1)`, as the table assumes `c = 1`, and the bounds `i`, `j` are natural numbers
with the side condition the subtraction needs.

## Inputs
* `φ₁` – left formula
* `φ₂` – right formula
* `i` – interval lower bound
* `j` – interval upper bound
* `ξ` – trace

## Hypotheses
* `hi` – the lower bound is positive
* `hij` – the bounds are ordered
* `h` – the rewritten formula holds

## Conclusion
* the until holds

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
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

theorem STL.rewrite_until_succ (φ₁ φ₂ : STL.Formula X) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j)
    (ξ : ℝ≥0 → X)
    (h : (φ₁.and ((STL.Formula.globOpen 1 φ₁).and
      (STL.Formula.next 1
        (STL.Formula.until ((i - 1 : ℕ) : ℝ≥0) ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))).Satisfies ξ)
    : -- --- CONCL ---
    (STL.Formula.until (i : ℝ≥0) (j : ℝ≥0) φ₁ φ₂).Satisfies ξ := by -- --- PROOF ---
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.Satisfies, Time.shift_shift,
    Nat.add_sub_cancel] at h ⊢
  obtain ⟨h₁, h₂, t, ht₁, ht₂, ht₃, ht₄⟩ := h
  refine ⟨t + 1, ?_, ?_, ?_, ?_⟩
  · push_cast; exact add_le_add ht₁ le_rfl
  · push_cast; exact add_le_add ht₂ le_rfl
  · exact ht₃
  · intro s hs
    rcases lt_trichotomy s 1 with hs1 | rfl | hs1
    · rcases eq_zero_or_pos s with rfl | hs0
      · rw [Time.shift_zero]; exact h₁
      · exact h₂ s hs0 hs1
    · have := ht₄ 0 (by simpa using hs)
      simpa using this
    · have := ht₄ (s - 1) (by rwa [tsub_lt_iff_right hs1.le])
      rwa [tsub_add_cancel_of_le hs1.le] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
