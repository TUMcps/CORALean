module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.ShiftShift
public import CORALean.Specification.STL.Theorems.ForallLtAddOneOfBlocks

@[expose] public section

/-!
# Rewriting, `G_I` of `U[0,j]`

[1, Table 1] `G_I(φ₁ U[0,j] φ₂) ⇐ G_I φ₂ ∨ (G_I φ₁ ∧ X₁(φ₂ ∨ (φ₁ ∧ G_I φ₁ ∧ G_I(φ₁ U[0,j-1]
φ₂))))` for `1 ≤ j`.

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
* always of the until from zero holds

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

theorem STL.rewrite_globOpen_until_zero (φ₁ φ₂ : STL.Formula X) (j : ℕ) (hj : 1 ≤ j) (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.globOpen 1 φ₂).or ((STL.Formula.globOpen 1 φ₁).and (STL.Formula.next 1
      (φ₂.or (φ₁.and ((STL.Formula.globOpen 1 φ₁).and (STL.Formula.globOpen 1
        (STL.Formula.until 0 ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))))))).Satisfies ξ) : -- --- CONCL ---
    (STL.Formula.globOpen 1 (STL.Formula.until 0 (j : ℝ≥0) φ₁ φ₂)).Satisfies
    ξ := by -- --- PROOF ---
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.Satisfies, Time.shift_shift,
    Nat.add_sub_cancel] at h ⊢
  intro s hs₀ hs₁
  rcases h with hG₂ | ⟨hG, hφ₂ | ⟨hφ, hG', hU⟩⟩
  · exact ⟨0, le_rfl, zero_le, by rw [zero_add]; exact hG₂ s hs₀ hs₁,
      fun t ht => absurd ht not_lt_zero⟩
  · -- the target holds at `1`, which is `1 - s` away from `s`
    refine ⟨1 - s, zero_le, ?_, ?_, ?_⟩
    · push_cast; exact tsub_le_self.trans le_add_self
    · rwa [tsub_add_cancel_of_le hs₁.le]
    · intro t' ht'
      exact hG _ (lt_of_lt_of_le hs₀ le_add_self) (lt_tsub_iff_right.1 ht')
  · obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ := hU s hs₀ hs₁
    refine ⟨t + 1, zero_le, ?_, ?_, ?_⟩
    · push_cast; exact add_le_add ht₂ le_rfl
    · have e : t + 1 + s = t + (s + 1) := by ring
      rw [e]; exact ht₃
    · exact Time.forall_lt_add_one_of_blocks (fun x => φ₁.Satisfies (Time.shift ξ x)) hs₀ hs₁ hG hφ
        hG'
        ht₄

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
