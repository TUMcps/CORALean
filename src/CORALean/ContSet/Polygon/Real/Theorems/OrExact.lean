module

public import CORALean.ContSet.Polygon.Real.Operations.Basic
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# `Polygon.or` is the union

Exactly, unlike `VPolytope.or`, which hulls: a polygon holds the union as a list of pieces.

## Inputs
* `P` – polygon
* `Q` – polygon

## Hypotheses
* none

## Conclusion
* `Polygon.or` is the union
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.or_exact (P Q : Polygon) :
    ContSet.construct P ∪ ContSet.construct Q =
      ContSet.construct (Polygon.or P Q) := by -- --- PROOF ---
  ext x
  simp only [Set.mem_union, SetUnion.mem_construct, Polygon.or, List.mem_append]
  constructor
  · rintro (⟨s, hs, hx⟩ | ⟨s, hs, hx⟩)
    · exact ⟨s, Or.inl hs, hx⟩
    · exact ⟨s, Or.inr hs, hx⟩
  · rintro ⟨s, hs | hs, hx⟩
    · exact Or.inl ⟨s, hs, hx⟩
    · exact Or.inr ⟨s, hs, hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
