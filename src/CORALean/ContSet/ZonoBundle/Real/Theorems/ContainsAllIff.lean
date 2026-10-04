import CORALean.ContSet.ZonoBundle.Real.Operations.ContainsAll

/-!
# A bundle contains a set iff every member does

A bundle denotes the intersection of its members, and `S` lies in an intersection exactly when it
lies in each intersectand, so CORA's member-wise `'exact:zonotope'` check is exact for every
operand `S`: nothing is lost, unlike the zonotope hull of a bundle.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.containsAll_iff (zB : ZonoBundle α) (S : Set α) :
    zB.containsAll S ↔ S ⊆ zB.construct :=
  Set.subset_iInter_iff.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
