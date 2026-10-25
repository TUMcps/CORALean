module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Operations.HasAllMembersFullDim
public import CORALean.ContSet.Zonotope.Real.Theorems.IsFullDimIff

@[expose] public section

/-!
# A full-dimensional bundle has full-dimensional members

The intersection lies in each member, so an interior point of the intersection is an interior
point of every member, whose generators then span (`Zonotope.isFullDim_iff`). Hence CORA's
early answers `false` of `@zonoBundle/isFullDim` are correct; the converse fails (two
full-dimensional zonotopes can meet in a lower-dimensional set), which is why CORA ends with the
test of the intersection polytope.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `h` – the bundle has an interior point

## Conclusion
* every member is full dimensional
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.allMembersFullDim_of_interior {zB : ZonoBundle α}
    (h : (interior zB.construct).Nonempty) : zB.HasAllMembersFullDim := fun i => by
  -- the intersection is inside member `i`
  have hsub : zB.construct ⊆ (zB.Z i).construct := SetIntersection.construct_subset_ofFn _ i
  exact (Zonotope.isFullDim_iff (zB.Z i)).mp (h.mono (interior_mono hsub))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
