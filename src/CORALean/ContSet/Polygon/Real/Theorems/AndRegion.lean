module

public import CORALean.ContSet.Polygon.Real.Polygon
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# The intersection of two polygons, piece by piece

Exactly: the intersection of two unions is the union of the pairwise piece intersections.

## Inputs
* `P` – polygon
* `Q` – polygon

## Hypotheses
* none

## Conclusion
* the intersection of two polygons is the union of the intersections of their pieces
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.and_region (P Q : Polygon) : -- --- CONCL ---
    ContSet.construct P ∩ ContSet.construct Q =
      ⋃ p ∈ P.sets, ⋃ q ∈ Q.sets,
        (VPolytope.construct p ∩ VPolytope.construct q) := by -- --- PROOF ---
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, SetUnion.mem_construct, exists_prop]
  constructor
  · rintro ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩
    exact ⟨p, hp, q, hq, hxp, hxq⟩
  · rintro ⟨p, hp, q, hq, hxp, hxq⟩
    exact ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
