module

public import CORALean.ContSet.Polygon.Real.Operations.IsIntersecting
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Theorems.InterNonemptyIff

@[expose] public section

/-!
# `Polygon.isIntersecting` is region intersection

Exactly: the regions share a point iff some pair of pieces does.

## Inputs
* `P` – polygon
* `Q` – polygon

## Hypotheses
* none

## Conclusion
* `Polygon.isIntersecting` is region intersection
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isIntersecting_iff (P Q : Polygon) :
    (ContSet.construct P ∩ ContSet.construct Q).Nonempty ↔
      Polygon.isIntersecting P Q := by -- --- PROOF ---
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hx
    obtain ⟨q, hq, hyq⟩ := SetUnion.mem_construct.mp hy
    exact ⟨p, hp, q, hq, (VPolytope.inter_nonempty_iff p q).mp ⟨x, hxp, hyq⟩⟩
  · rintro ⟨p, hp, q, hq, h⟩
    obtain ⟨x, hxp, hxq⟩ := (VPolytope.inter_nonempty_iff p q).mpr h
    exact ⟨x, SetUnion.mem_construct.mpr ⟨p, hp, hxp⟩, SetUnion.mem_construct.mpr ⟨q, hq, hxq⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
