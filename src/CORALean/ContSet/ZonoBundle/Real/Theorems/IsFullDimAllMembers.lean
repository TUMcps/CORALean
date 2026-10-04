import CORALean.ContSet.ZonoBundle.Real.Operations.AllMembersFullDim
import CORALean.ContSet.Zonotope.Real.Theorems.IsFullDimIff

/-!
# A full-dimensional bundle has full-dimensional members

The intersection lies in each member, so an interior point of the intersection is an interior
point of every member, whose generators then span (`Zonotope.isFullDim_iff`). Hence CORA's
early answers `false` of `@zonoBundle/isFullDim` are correct; the converse fails (two
full-dimensional zonotopes can meet in a lower-dimensional set), which is why CORA ends with the
test of the intersection polytope.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.allMembersFullDim_of_interior {zB : ZonoBundle α}
    (h : (interior zB.construct).Nonempty) : zB.allMembersFullDim := fun i => by
  -- the intersection is inside member `i`
  have hsub : zB.construct ⊆ (zB.Z i).construct := Set.iInter_subset _ i
  exact (Zonotope.isFullDim_iff (zB.Z i)).mp (h.mono (interior_mono hsub))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
