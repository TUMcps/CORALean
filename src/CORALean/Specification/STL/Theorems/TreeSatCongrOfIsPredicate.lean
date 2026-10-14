module

public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# A predicate depends on the initial state only

A formula that passes `isPredicate` is satisfied by a trace according to its state at time `0`:
two traces with the same initial state satisfy it together.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_congr_of_isPredicate (φ : STL.Tree n) (h : φ.isPredicate = true)
    (ξ ξ' : ℝ≥0 → Fin n → ℝ) (hξ : ξ 0 = ξ' 0) : φ.Sat ξ ↔ φ.Sat ξ' := by -- --- PROOF ---
  induction φ with
  | cmp op e₁ e₂ => simp [STL.Tree.Sat, hξ]
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.isPredicate, Bool.and_eq_true] at h
    simp [STL.Tree.Sat, ihφ h.1, ihψ h.2]
  | _ => simp [STL.Tree.isPredicate] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
