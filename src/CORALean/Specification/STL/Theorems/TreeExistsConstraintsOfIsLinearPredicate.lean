module

public import CORALean.Specification.STL.Operations.TreeIsLinearPredicate
public import CORALean.Specification.STL.Theorems.ExprExistsAffineOfIsLinear
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A linear predicate is a finite list of linear constraints

A formula that passes `isLinearPredicate` is satisfied by a trace exactly when its initial state
meets finitely many constraints `op (Σᵢ aᵢ xᵢ) b`, one per comparison: the set of states it
describes is an intersection of open and closed halfspaces.

## Inputs
* `φ` – formula

## Hypotheses
* `h` – the formula is a linear predicate

## Conclusion
* the formula is equivalent to a finite list of linear constraints
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped BigOperators NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.exists_constraints_of_isLinearPredicate (φ : STL.Tree n)
    (h : φ.isLinearPredicate = true) : ∃ L : List (STL.Cmp × (Fin n → ℝ) × ℝ),
      ∀ ξ : ℝ≥0 → Fin n → ℝ,
        φ.Sat ξ ↔ ∀ c ∈ L, c.1.rel (∑ i, c.2.1 i * ξ 0 i) c.2.2 := by -- --- PROOF ---
  induction φ with
  | cmp op e₁ e₂ =>
    simp only [STL.Tree.isLinearPredicate, Bool.and_eq_true] at h
    obtain ⟨a₁, b₁, h₁⟩ := STL.Expr.exists_affine_of_isLinear e₁ h.1
    obtain ⟨a₂, b₂, h₂⟩ := STL.Expr.exists_affine_of_isLinear e₂ h.2
    refine ⟨[(op, fun i => a₁ i - a₂ i, b₂ - b₁)], fun ξ => ?_⟩
    simp only [STL.Tree.Sat, h₁, h₂, sub_mul, Finset.sum_sub_distrib, List.mem_singleton,
      forall_eq]
    cases op <;> simp only [STL.Cmp.rel] <;> constructor <;> intro <;> linarith
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.isLinearPredicate, Bool.and_eq_true] at h
    obtain ⟨L₁, hL₁⟩ := ihφ h.1
    obtain ⟨L₂, hL₂⟩ := ihψ h.2
    exact ⟨L₁ ++ L₂, fun ξ => by simp [STL.Tree.Sat, hL₁ ξ, hL₂ ξ, or_imp, forall_and]⟩
  | _ => simp [STL.Tree.isLinearPredicate] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
