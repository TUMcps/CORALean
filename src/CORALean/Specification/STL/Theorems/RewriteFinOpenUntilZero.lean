module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.ShiftShift
public import CORALean.Specification.STL.Theorems.ForallLtAddOneOfBlocks

@[expose] public section

/-!
# Rewriting, `F_I` of `U[0,j]`

[1, Table 1] `F_I(φ₁ U[0,j] φ₂) ⇐ F_I φ₂ ∨ (G_I φ₁ ∧ X₁(φ₂ ∨ (φ₁ ∧ G_I φ₁ ∧ F_I(φ₁ U[0,j-1]
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
* eventually of the until from zero holds

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

theorem STL.rewrite_finOpen_until_zero (φ₁ φ₂ : STL.Formula X) (j : ℕ) (hj : 1 ≤ j) (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.finOpen 1 φ₂).or ((STL.Formula.globOpen 1 φ₁).and (STL.Formula.next 1
      (φ₂.or (φ₁.and ((STL.Formula.globOpen 1 φ₁).and (STL.Formula.finOpen 1
        (STL.Formula.until 0 ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))))))).Sat ξ) : -- --- CONCL ---
    (STL.Formula.finOpen 1 (STL.Formula.until 0 (j : ℝ≥0) φ₁ φ₂)).Sat ξ := by -- --- PROOF ---
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.Sat, Time.shift_shift,
    Nat.add_sub_cancel] at h ⊢
  rcases h with ⟨s, hs₀, hs₁, hs₂⟩ | ⟨hG, hφ₂ | ⟨hφ, hG', s, hs₀, hs₁, t, ht₁, ht₂, ht₃, ht₄⟩⟩
  · refine ⟨s, hs₀, hs₁, 0, le_rfl, zero_le, ?_, fun t ht => absurd ht not_lt_zero⟩
    rwa [zero_add]
  · -- the target holds at `1`: half a step brings the trace there
    have h2 : (0 : ℝ≥0) < 2⁻¹ := by norm_num
    have h2' : (2⁻¹ : ℝ≥0) < 1 := by norm_num
    have hh : (2⁻¹ : ℝ≥0) + 2⁻¹ = 1 := by rw [← two_mul]; exact mul_inv_cancel₀ two_ne_zero
    refine ⟨2⁻¹, h2, h2', 2⁻¹, zero_le, ?_, ?_, ?_⟩
    · push_cast; exact (h2'.le).trans (le_add_self)
    · rwa [hh]
    · intro t' ht'
      have := add_lt_add_of_lt_of_le ht' (le_refl (2⁻¹ : ℝ≥0))
      rw [hh] at this
      exact hG _ (lt_of_lt_of_le h2 le_add_self) this
  · refine ⟨s, hs₀, hs₁, t + 1, zero_le, ?_, ?_, ?_⟩
    · push_cast; exact add_le_add ht₂ le_rfl
    · have e : t + 1 + s = t + (s + 1) := by ring
      rw [e]; exact ht₃
    · exact Time.forall_lt_add_one_of_blocks (fun x => φ₁.Sat (Time.shift ξ x)) hs₀ hs₁ hG hφ hG'
        ht₄

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
