module

public import CORALean.ContSet.EmptySet.Real.Instances
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The empty set contains exactly the empty sets

CORA's `@emptySet/contains_` answers `true` iff the other set is empty. The representation has
no emptiness test for an arbitrary `S`, so there is no `Contains` instance; this is the
statement the answer would be sound and complete for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.contains_iff {S : Type} [ContSet S (Vec ℝ n)] (E : EmptySet n) (s : S) :
    ContSet.construct s ⊆ E.construct ↔ ContSet.construct s = ∅ :=
  Set.subset_empty_iff

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
