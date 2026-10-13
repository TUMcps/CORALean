module

public import CORALean.ContSet.Fullspace.Real.Fullspace
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The full space meets exactly the nonempty sets

CORA's `@fullspace/isIntersecting_` answers `true` iff the other set is nonempty. The
representation has no emptiness test for an arbitrary `S`, so there is no `IsDisjoint` instance;
this is the statement the answer would be sound and complete for.
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

theorem Fullspace.disjoint_iff {S : Type} [ContSet S (Vec ℝ n)] (F : Fullspace n) (s : S) :
    Disjoint (ContSet.construct s) F.construct ↔ ContSet.construct s = ∅ :=
  Set.disjoint_univ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
