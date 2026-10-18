module

public import Mathlib.Data.List.OfFn
public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Operations.ContainsAll

@[expose] public section

/-!
# A bundle contains a set iff every member does

A bundle denotes the intersection of its members, and `S` lies in an intersection exactly when it
lies in each intersectand, so CORA's member-wise `'exact:zonotope'` check is exact for every
operand `S`: nothing is lost, unlike the zonotope hull of a bundle.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.containsAll_iff (zB : ZonoBundle α) (S : Set α) :
    zB.containsAll S ↔ S ⊆ zB.construct :=
  ((SetIntersection.subset_construct_iff (I := zB.toSetIntersection)).trans
    List.forall_mem_ofFn_iff).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
