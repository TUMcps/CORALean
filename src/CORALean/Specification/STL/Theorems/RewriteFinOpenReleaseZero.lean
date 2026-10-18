module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.SatRelease
public import CORALean.Specification.STL.Theorems.ShiftShift
public import CORALean.Specification.STL.Theorems.ForallLtTwoOfBlocks

@[expose] public section

/-!
# Rewriting, `F_I` of `R[0,j]`

[1, Table 1] `F_I(φ₁ R[0,j] φ₂) ⇐ F_I(φ₁ ∧ φ₂) ∨ (G_I φ₂ ∧ X₁(φ₂ ∧ (φ₁ ∨ (G_I φ₂ ∧ F_I(φ₁ R[0,j-1]
φ₂)))))` for `1 ≤ j`, reading the printed `F_I φ₁ R[0,j-1] φ₂` as `F_I(φ₁ R[0,j-1] φ₂)`.

The window is `I = (0,1)`, as the table assumes `c = 1`, and the bounds `i`, `j` are natural numbers
with the side condition the subtraction needs.

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

theorem STL.rewrite_finOpen_release_zero (φ₁ φ₂ : STL.Formula X) (j : ℕ) (hj : 1 ≤ j) (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.finOpen 1 (φ₁.and φ₂)).or ((STL.Formula.globOpen 1 φ₂).and
      (STL.Formula.next 1 (φ₂.and (φ₁.or ((STL.Formula.globOpen 1 φ₂).and (STL.Formula.finOpen 1
        (STL.Formula.release 0 ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))))))).Sat ξ) : -- --- STMT ---
    (STL.Formula.finOpen 1 (STL.Formula.release 0 (j : ℝ≥0) φ₁ φ₂)).Sat ξ := by -- --- PROOF ---
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.sat_release,
    STL.Formula.Sat, Time.shift_shift, Nat.add_sub_cancel] at h ⊢
  have h2 : (0 : ℝ≥0) < 2⁻¹ := by norm_num
  have h2' : (2⁻¹ : ℝ≥0) < 1 := by norm_num
  have hh : (2⁻¹ : ℝ≥0) + 2⁻¹ = 1 := by rw [← two_mul]; exact mul_inv_cancel₀ two_ne_zero
  rcases h with ⟨s, hs₀, hs₁, hφ₁, hφ₂⟩ | ⟨hG, hφ₂, hφ₁ | ⟨hG', s, hs₀, hs₁, hR⟩⟩
  · refine ⟨s, hs₀, hs₁, fun t _ _ => ?_⟩
    rcases eq_zero_or_pos t with rfl | ht
    · exact Or.inl (by rwa [zero_add])
    · exact Or.inr ⟨0, ht, by rwa [zero_add]⟩
  · -- `φ₁` holds at `1`: from offset `1/2`, the point `1` is `1/2` into the window
    refine ⟨2⁻¹, h2, h2', fun t _ _ => ?_⟩
    rcases lt_trichotomy (t + 2⁻¹) 1 with hp | hp | hp
    · exact Or.inl (hG _ (lt_of_lt_of_le h2 le_add_self) hp)
    · exact Or.inl (by rw [hp]; exact hφ₂)
    · refine Or.inr ⟨2⁻¹, ?_, by rwa [hh]⟩
      rw [← hh] at hp
      exact lt_of_add_lt_add_right hp
  · refine ⟨s, hs₀, hs₁, fun t _ ht₂ => ?_⟩
    rcases lt_or_ge t 1 with ht | ht
    · refine Or.inl (Time.forall_lt_two_of_blocks (fun x => φ₂.Sat (Time.shift ξ x)) hG hφ₂
        (by simpa using hG') (t + s) (lt_of_lt_of_le hs₀ le_add_self) ?_)
      calc t + s < 1 + 1 := add_lt_add ht hs₁
        _ = 2 := one_add_one_eq_two
    · obtain ⟨d, rfl⟩ := exists_add_of_le ht
      push_cast at ht₂
      rw [add_comm 1 d] at ht₂
      rcases hR d zero_le (le_of_add_le_add_right ht₂) with h' | ⟨k, hk, hk'⟩
      · exact Or.inl (by rwa [show 1 + d + s = d + (s + 1) by ring])
      · exact Or.inr ⟨1 + k, by simpa using hk, by rwa [show 1 + k + s = k + (s + 1) by ring]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
