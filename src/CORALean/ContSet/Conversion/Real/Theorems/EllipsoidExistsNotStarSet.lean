module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidExistsNotHPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.StarSetExistsHPolytopeExact

@[expose] public section

/-!
# An ellipsoid that is no star set

A star set is a halfspace description (`StarSet.exists_hPolytope_exact`), which the unit disc is not
(`Ellipsoid.exists_not_hPolytope`). So the star sets, convex sets of linear predicates on the
factors, do not contain the ellipsoids, which are among the sets a support function represents.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.exists_not_starSet :
    ∃ E : Ellipsoid 2, ¬ ∃ s : StarSet 2, s.construct = E.construct := by
  obtain ⟨E, hE⟩ := Ellipsoid.exists_not_hPolytope
  exact ⟨E, fun ⟨s, hs⟩ => hE (hs ▸ StarSet.exists_hPolytope_exact s)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
