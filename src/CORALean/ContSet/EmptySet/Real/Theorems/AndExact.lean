module

public import CORALean.ContSet.EmptySet.Real.Operations.And
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.and_` is exact

Intersecting `∅` with a set of any representation gives `∅`, so the returned empty set
denotes the intersection of the two operands, exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.and_exact {S : Type} [ContSet S (Vec ℝ n)] (E : EmptySet n) (s : S) :
    ContSet.construct (E.and_ s) = ContSet.construct E ∩ ContSet.construct s := by
  change (∅ : Set (Vec ℝ n)) = ∅ ∩ ContSet.construct s
  exact (Set.empty_inter _).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
