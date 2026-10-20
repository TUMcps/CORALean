module

public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeTemporal

@[expose] public section

/-!
# A predicate has no temporal operator

A formula that passes `isPredicate` is not temporal, so `isPredicate.m`'s first test
(`obj.temporal`) is implied by its recursion.

## Inputs
* `φ` – formula

## Hypotheses
* `h` – the formula is a predicate

## Conclusion
* the formula has no temporal operator
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

theorem STL.Tree.temporal_of_isPredicate (φ : STL.Tree n) (h : φ.isPredicate = true) :
    φ.temporal = false := by
  induction φ with
  | cmp => rfl
  | and φ ψ ihφ ihψ => simp_all [STL.Tree.isPredicate, STL.Tree.temporal]
  | _ => simp [STL.Tree.isPredicate] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
