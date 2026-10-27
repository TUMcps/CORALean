module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.ShiftShift
public import CORALean.Specification.STL.Theorems.ForallLtAddOneOfBlocks

@[expose] public section

/-!
# Rewriting, `G_I` of `U[i,j]`

[1, Table 1] `G_I(φ₁ U[i,j] φ₂) ⇐ G_I φ₁ ∧ X₁(φ₁ ∧ G_I φ₁ ∧ G_I(φ₁ U[i-1,j-1] φ₂))` for `1 ≤ i ≤ j`.

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
* always of the until holds

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

theorem STL.rewrite_globOpen_until_succ (φ₁ φ₂ : STL.Formula X) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j)
    (ξ : ℝ≥0 → X)
    (h : ((STL.Formula.globOpen 1 φ₁).and (STL.Formula.next 1 (φ₁.and
      ((STL.Formula.globOpen 1 φ₁).and (STL.Formula.globOpen 1
        (STL.Formula.until ((i - 1 : ℕ) : ℝ≥0) ((j - 1 : ℕ) : ℝ≥0) φ₁ φ₂)))))).Satisfies ξ)
    : -- --- CONCL ---
    (STL.Formula.globOpen 1
      (STL.Formula.until (i : ℝ≥0) (j : ℝ≥0) φ₁ φ₂)).Satisfies ξ := by -- --- PROOF ---
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [STL.Formula.sat_and, STL.Formula.sat_next, STL.Formula.Satisfies, Time.shift_shift,
    Nat.add_sub_cancel] at h ⊢
  obtain ⟨hG, hφ, hG', hU⟩ := h
  intro s hs₀ hs₁
  obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ := hU s hs₀ hs₁
  refine ⟨t + 1, ?_, ?_, ?_, ?_⟩
  · push_cast; exact add_le_add ht₁ le_rfl
  · push_cast; exact add_le_add ht₂ le_rfl
  · have e : t + 1 + s = t + (s + 1) := by ring
    rw [e]; exact ht₃
  · exact Time.forall_lt_add_one_of_blocks (fun x => φ₁.Satisfies (Time.shift ξ x)) hs₀ hs₁ hG hφ
      hG' ht₄

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
