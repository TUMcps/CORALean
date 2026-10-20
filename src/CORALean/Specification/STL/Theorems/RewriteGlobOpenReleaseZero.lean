module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.SatRelease
public import CORALean.Specification.STL.Theorems.ShiftShift
public import CORALean.Specification.STL.Theorems.ForallLtTwoOfBlocks

@[expose] public section

/-!
# Rewriting, `G_I` of `R[0,j]`

[1, Table 1] `G_I(φ₁ R[0,j] φ₂) ⇐ G_I φ₂ ∧ (G_I φ₁ ∨ X₁(φ₂ ∧ (φ₁ ∨ (G_I φ₂ ∧ G_I(φ₁ R[0,j-1]
φ₂)))))` for `1 ≤ j`.

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
* always of the release from zero holds

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

theorem STL.rewrite_globOpen_release_zero (φ₁ φ₂ : STL.Formula X) (j : ℕ) (hj : 1 ≤ j) (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.globOpen 1 φ₂).and ((STL.Formula.globOpen 1 φ₁).or (STL.Formula.next 1
      (φ₂.and (φ₁.or ((STL.Formula.globOpen 1 φ₂).and (STL.Formula.globOpen 1
        (STL.Formula.release 0 ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))))))).Sat ξ) : -- --- CONCL ---
    (STL.Formula.globOpen 1 (STL.Formula.release 0 (j : ℝ≥0) φ₁ φ₂)).Sat ξ := by -- --- PROOF ---
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.sat_release,
    STL.Formula.Sat, Time.shift_shift, Nat.add_sub_cancel] at h ⊢
  obtain ⟨hG₂, hG | ⟨hφ₂, hφ₁ | ⟨hG', hR⟩⟩⟩ := h
  · intro s hs₀ hs₁ t _ _
    rcases eq_zero_or_pos t with rfl | ht
    · exact Or.inl (by rw [zero_add]; exact hG₂ s hs₀ hs₁)
    · exact Or.inr ⟨0, ht, by rw [zero_add]; exact hG s hs₀ hs₁⟩
  · intro s hs₀ hs₁ t _ _
    rcases lt_trichotomy (t + s) 1 with hp | hp | hp
    · exact Or.inl (hG₂ _ (lt_of_lt_of_le hs₀ le_add_self) hp)
    · exact Or.inl (by rw [hp]; exact hφ₂)
    · -- past `1`, `φ₁` at `1` is `1 - s < t` into the window
      refine Or.inr ⟨1 - s, ?_, by rw [tsub_add_cancel_of_le hs₁.le]; exact hφ₁⟩
      rw [tsub_lt_iff_right hs₁.le]
      exact hp
  · intro s hs₀ hs₁ t _ ht₂
    rcases lt_or_ge t 1 with ht | ht
    · refine Or.inl (Time.forall_lt_two_of_blocks (fun x => φ₂.Sat (Time.shift ξ x)) hG₂ hφ₂
        (by simpa using hG') (t + s) (lt_of_lt_of_le hs₀ le_add_self) ?_)
      calc t + s < 1 + 1 := add_lt_add ht hs₁
        _ = 2 := one_add_one_eq_two
    · obtain ⟨d, rfl⟩ := exists_add_of_le ht
      push_cast at ht₂
      rw [add_comm 1 d] at ht₂
      rcases hR s hs₀ hs₁ d zero_le (le_of_add_le_add_right ht₂) with h' | ⟨k, hk, hk'⟩
      · exact Or.inl (by rwa [show 1 + d + s = d + (s + 1) by ring])
      · exact Or.inr ⟨1 + k, by simpa using hk, by rwa [show 1 + k + s = k + (s + 1) by ring]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
