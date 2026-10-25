module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.SatRelease
public import CORALean.Specification.STL.Theorems.ShiftShift

@[expose] public section

/-!
# Rewriting, `G_I` of `R[i,j]`

[1, Table 1] `G_I(φ₁ R[i,j] φ₂) ⇐ G_I φ₁ ∨ X₁(φ₁ ∨ G_I(φ₁ R[i-1,j-1] φ₂))` for `1 ≤ i ≤ j`.

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
* always of the release holds

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

theorem STL.rewrite_globOpen_release_succ (φ₁ φ₂ : STL.Formula X) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i ≤ j)
    (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.globOpen 1 φ₁).or (STL.Formula.next 1 (φ₁.or (STL.Formula.globOpen 1
      (STL.Formula.release ((i - 1 : ℕ) : ℝ≥0) ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂))))).Satisfies ξ)
    : -- --- CONCL ---
    (STL.Formula.globOpen 1
      (STL.Formula.release (i : ℝ≥0) (j : ℝ≥0) φ₁ φ₂)).Satisfies ξ := by -- --- PROOF ---
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_next, STL.Formula.sat_release, STL.Formula.Satisfies, Time.shift_shift,
    Nat.add_sub_cancel] at h ⊢
  intro s hs₀ hs₁ t ht₁ ht₂
  -- every `t ≥ i + 1` is at least `1`
  have ht1 : (1 : ℝ≥0) ≤ t := le_trans (by push_cast; exact le_add_self) ht₁
  rcases h with hG | hφ | hR
  · exact Or.inr ⟨0, lt_of_lt_of_le zero_lt_one ht1, by rw [zero_add]; exact hG s hs₀ hs₁⟩
  · -- `φ₁` holds at `1`, which is `1 - s < 1 ≤ t` after `s`
    exact Or.inr ⟨1 - s, lt_of_lt_of_le (tsub_lt_self zero_lt_one hs₀) ht1,
      by rw [tsub_add_cancel_of_le hs₁.le]; exact hφ⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le ht1
    push_cast at ht₁ ht₂
    rw [add_comm 1 d] at ht₁ ht₂
    rcases hR s hs₀ hs₁ d (le_of_add_le_add_right ht₁) (le_of_add_le_add_right ht₂) with
      h' | ⟨k, hk, hk'⟩
    · exact Or.inl (by rwa [show 1 + d + s = d + (s + 1) by ring])
    · exact Or.inr ⟨1 + k, by simpa using hk, by rwa [show 1 + k + s = k + (s + 1) by ring]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
