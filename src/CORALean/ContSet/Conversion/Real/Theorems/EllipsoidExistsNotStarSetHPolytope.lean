module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidExistsNotHPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.StarSetExistsHPolytopeExact

@[expose] public section

/-!
# An ellipsoid that is no star set of CORA's predicate

A star set whose predicate is CORA's polytope `C α ≤ d`, on its box `l ≤ α ≤ u`, is a halfspace
description (`StarSet.exists_hPolytope_exact`), which the unit disc is not
(`Ellipsoid.exists_not_hPolytope`). So the linear predicate does not reach the ellipsoids; a star
set with a level-set or support-function predicate does (`SupportFunction.starSet_exact`).-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The unit disc is no star set with a polytope predicate. -/
theorem Ellipsoid.exists_not_starSet_hPolytope :
    ∃ E : Ellipsoid 2, ¬ ∃ s : StarSet ℋ𝒫 2, s.construct = E.construct := by
  obtain ⟨E, hE⟩ := Ellipsoid.exists_not_hPolytope
  exact ⟨E, fun ⟨s, hs⟩ => hE (hs ▸ StarSet.exists_hPolytope_exact s)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
