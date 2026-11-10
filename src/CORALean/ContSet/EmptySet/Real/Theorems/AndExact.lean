module

public import CORALean.ContSet.EmptySet.Real.Operations.And
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.and_` is exact

Intersecting `∅` with a set of any representation gives `∅`, so the returned empty set
denotes the intersection of the two operands, exactly.

## Inputs
* `S` – type of the other operand
* `E` – empty set
* `s` – other operand

## Hypotheses
* none

## Conclusion
* `and_` denotes the intersection of both operands exactly
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet ContSetLike

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.and_exact {S : Type} [ContSetLike S (Vec ℝ n)] (E : EmptySet n) (s : S) :
    ContSetLike.toSet (E.and_ s) = ContSetLike.toSet E ∩ ContSetLike.toSet s := by
  change (∅ : Set (Vec ℝ n)) = ∅ ∩ ContSetLike.toSet s
  exact (Set.empty_inter _).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
