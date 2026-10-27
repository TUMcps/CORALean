module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.SatRelease
public import CORALean.Specification.STL.Theorems.ShiftShift
public import CORALean.Specification.STL.Theorems.ShiftZero

@[expose] public section

/-!
# Rewriting, `R[0,j]`

[1, Table 1] `φ₁ R[0,j] φ₂ ⇐ φ₂ ∧ (φ₁ ∨ (G_I φ₂ ∧ (F_I φ₁ ∨ X₁(φ₁ R[0,j-1] φ₂))))` for `1 ≤ j`.

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
* the release from zero holds

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

theorem STL.rewrite_release_zero (φ₁ φ₂ : STL.Formula X) (j : ℕ) (hj : 1 ≤ j) (ξ : ℝ≥0 → X)
    (h : (φ₂.and (φ₁.or ((STL.Formula.globOpen 1 φ₂).and ((STL.Formula.finOpen 1 φ₁).or
      (STL.Formula.next 1 (STL.Formula.release 0 ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))))).Satisfies ξ)
    : -- --- CONCL ---
    (STL.Formula.release 0 (j : ℝ≥0) φ₁ φ₂).Satisfies ξ := by -- --- PROOF ---
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.sat_release,
    STL.Formula.Satisfies, Time.shift_shift, Nat.add_sub_cancel] at h ⊢
  obtain ⟨h₂, h₁ | ⟨hG, hF | hX⟩⟩ := h
  · intro t _ ht
    rcases eq_zero_or_pos t with rfl | ht0
    · exact Or.inl (by rwa [Time.shift_zero])
    · exact Or.inr ⟨0, ht0, by rwa [Time.shift_zero]⟩
  · -- `F_I φ₁` covers every time past `1`, `G_I φ₂` the times before it
    intro t _ ht
    rcases eq_zero_or_pos t with rfl | ht0
    · exact Or.inl (by rwa [Time.shift_zero])
    rcases lt_or_ge t 1 with ht1 | ht1
    · exact Or.inl (hG t ht0 ht1)
    · obtain ⟨s, hs₀, hs₁, hs₂⟩ := hF
      exact Or.inr ⟨s, hs₁.trans_le ht1, hs₂⟩
  · -- past `1`, the time is `1 + d` and the next-operator's release applies at `d`
    intro t _ ht
    rcases eq_zero_or_pos t with rfl | ht0
    · exact Or.inl (by rwa [Time.shift_zero])
    rcases lt_or_ge t 1 with ht1 | ht1
    · exact Or.inl (hG t ht0 ht1)
    · obtain ⟨d, rfl⟩ := exists_add_of_le ht1
      push_cast at ht
      rw [add_comm 1 d] at ht
      rcases hX d (zero_le) (le_of_add_le_add_right ht) with h' | ⟨k, hk, hk'⟩
      · exact Or.inl (by rwa [add_comm] at h')
      · exact Or.inr ⟨1 + k, by simpa using hk, by rwa [add_comm] at hk'⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
