module

public import CORALean.ContSet.Polygon.Real.Operations.IsequalPieces
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# `Polygon.isequalPieces` implies equal regions

Sound only; the converse is not claimed (the note on `Polygon.isequalPieces`).

## Inputs
* `P` – polygon
* `Q` – polygon

## Hypotheses
* `h` – `isequalPieces` answers `true` for `P` and `Q`

## Conclusion
* `Polygon.isequalPieces` implies equal regions
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isequalPieces_sound {P Q : Polygon} (h : Polygon.isequalPieces P Q) :
    ContSet.construct P = ContSet.construct Q := by -- --- PROOF ---
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hx
    obtain ⟨q, hq, hpq⟩ := h.1 p hp
    exact SetUnion.mem_construct.mpr ⟨q, hq, hpq hxp⟩
  · intro x hx
    obtain ⟨q, hq, hxq⟩ := SetUnion.mem_construct.mp hx
    obtain ⟨p, hp, hqp⟩ := h.2 q hq
    exact SetUnion.mem_construct.mpr ⟨p, hp, hqp hxq⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
