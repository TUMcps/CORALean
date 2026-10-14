module

public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeIsLinearPredicate

@[expose] public section

/-!
# A linear predicate is a predicate

A formula that passes `isLinearPredicate` passes `isPredicate`.
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

theorem STL.Tree.isPredicate_of_isLinearPredicate (φ : STL.Tree n)
    (h : φ.isLinearPredicate = true) : φ.isPredicate = true := by
  induction φ with
  | cmp => rfl
  | and φ ψ ihφ ihψ => simp_all [STL.Tree.isLinearPredicate, STL.Tree.isPredicate]
  | _ => simp [STL.Tree.isLinearPredicate] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
