import CORALean.Specification.STL.STL
import CORALean.Specification.STL.Theorems.SatAnd
import CORALean.Specification.STL.Theorems.SatNext
import CORALean.Specification.STL.Theorems.SatRelease
import CORALean.Specification.STL.Theorems.ShiftShift
import CORALean.Specification.STL.Theorems.ShiftZero

/-!
# Rewriting, `R[0,j]`

[1, Table 1] `φ₁ R[0,j] φ₂ ⇐ φ₂ ∧ (φ₁ ∨ (G_I φ₂ ∧ (F_I φ₁ ∨ X₁(φ₁ R[0,j-1] φ₂))))` for `1 ≤ j`.

The window is `I = (0,1)`, as the table assumes `c = 1`, and the bounds `i`, `j` are natural numbers
with the side condition the subtraction needs.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.rewrite_release_zero (φ₁ φ₂ : STL.Formula X) (j : ℕ) (hj : 1 ≤ j) (ξ : ℝ≥0 → X)
    (h : (φ₂.and (φ₁.or ((STL.Formula.globOpen 1 φ₂).and ((STL.Formula.finOpen 1 φ₁).or
      (STL.Formula.next 1 (STL.Formula.release 0 ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))))).Sat ξ) :
    (STL.Formula.release 0 (j : ℝ≥0) φ₁ φ₂).Sat ξ := by -- --- PROOF ---
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.sat_release,
    STL.Formula.Sat, Time.shift_shift, Nat.add_sub_cancel] at h ⊢
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
