module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.SatRelease
public import CORALean.Specification.STL.Theorems.ShiftShift

@[expose] public section

/-!
# Rewriting, `F_I` of `R[i,j]`

[1, Table 1] `F_I(φ₁ R[i,j] φ₂) ⇐ F_I φ₁ ∨ X₁(φ₁ ∨ F_I φ₁ ∨ F_I(φ₁ R[i-1,j-1] φ₂))` for `1 ≤ i ≤ j`.

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

theorem STL.rewrite_finOpen_release_succ (φ₁ φ₂ : STL.Formula X) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i ≤ j)
    (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.finOpen 1 φ₁).or (STL.Formula.next 1 (φ₁.or ((STL.Formula.finOpen 1 φ₁).or
      (STL.Formula.finOpen 1
        (STL.Formula.release ((i - 1 : ℕ) : ℝ≥0) ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))))).Sat ξ) :
    (STL.Formula.finOpen 1
      (STL.Formula.release (i : ℝ≥0) (j : ℝ≥0) φ₁ φ₂)).Sat ξ := by -- --- PROOF ---
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_next, STL.Formula.sat_release, STL.Formula.Sat, Time.shift_shift,
    Nat.add_sub_cancel] at h ⊢
  have h2 : (0 : ℝ≥0) < 2⁻¹ := by norm_num
  have h2' : (2⁻¹ : ℝ≥0) < 1 := by norm_num
  have hh : (2⁻¹ : ℝ≥0) + 2⁻¹ = 1 := by rw [← two_mul]; exact mul_inv_cancel₀ two_ne_zero
  -- every `t ≥ i + 1` is at least `1`
  have ht1 : ∀ t : ℝ≥0, ((i + 1 : ℕ) : ℝ≥0) ≤ t → (1 : ℝ≥0) ≤ t := fun t ht =>
    le_trans (by push_cast; exact le_add_self) ht
  rcases h with ⟨s, hs₀, hs₁, hs₂⟩ | h | ⟨s, hs₀, hs₁, hs₂⟩ | ⟨s, hs₀, hs₁, hs₂⟩
  · refine ⟨s, hs₀, hs₁, fun t ht _ => Or.inr ⟨0, lt_of_lt_of_le zero_lt_one (ht1 t ht), ?_⟩⟩
    rwa [zero_add]
  · refine ⟨2⁻¹, h2, h2', fun t ht _ => Or.inr ⟨2⁻¹, h2'.trans_le (ht1 t ht), ?_⟩⟩
    rwa [hh]
  · -- `φ₁` holds `s + 1` in: step to the midpoint of `(s, 1)`, which is `1 - (s + 1)/2` earlier
    have hs : (s + 1) / 2 < 1 := by
      rw [div_lt_one two_pos]
      calc s + 1 < 1 + 1 := add_lt_add_of_lt_of_le hs₁ le_rfl
        _ = 2 := one_add_one_eq_two
    refine ⟨(s + 1) / 2, by positivity, hs, fun t ht _ => ?_⟩
    refine Or.inr ⟨(s + 1) / 2, hs.trans_le (ht1 t ht), ?_⟩
    rwa [add_halves]
  · refine ⟨s, hs₀, hs₁, fun t ht₁ ht₂ => ?_⟩
    obtain ⟨d, rfl⟩ := exists_add_of_le (ht1 t ht₁)
    push_cast at ht₁ ht₂
    rw [add_comm 1 d] at ht₁ ht₂
    rcases hs₂ d (le_of_add_le_add_right ht₁) (le_of_add_le_add_right ht₂) with h' | ⟨k, hk, hk'⟩
    · exact Or.inl (by rwa [show 1 + d + s = d + (s + 1) by ring])
    · exact Or.inr ⟨1 + k, by simpa using hk, by rwa [show 1 + k + s = k + (s + 1) by ring]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
