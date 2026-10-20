module

public import CORALean.ContSet.Polygon.Float.Operations.And
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Float.Theorems.IntersectionOuter

@[expose] public section

/-!
# `Polygon.and` encloses the intersection

A common point lies in a piece of each polygon, so in their pair's intersection
(`VPolytope.intersection_outer`), which is a piece of the result. Outer only.

## Inputs
* `P` – polygon
* `Q` – polygon

## Hypotheses
* none

## Conclusion
* `Polygon.and` encloses the intersection
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.and_outer (P Q : Polygon 𝕋) : -- --- CONCL ---
    ContSet.construct P ∩ ContSet.construct Q ⊆
      ContSet.construct (Polygon.and P Q) := by -- --- PROOF ---
  rintro x ⟨hP, hQ⟩
  -- a piece of each polygon holds the point
  obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hP
  obtain ⟨q, hq, hxq⟩ := SetUnion.mem_construct.mp hQ
  -- and so does their intersection, a piece of the result
  exact SetUnion.mem_construct.mpr ⟨p.intersection q,
    List.mem_map.mpr ⟨(p, q), List.pair_mem_product.mpr ⟨hp, hq⟩, rfl⟩,
    VPolytope.intersection_outer p q ⟨hxp, hxq⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
