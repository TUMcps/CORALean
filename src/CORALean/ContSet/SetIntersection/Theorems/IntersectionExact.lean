module

public import CORALean.ContSet.SetIntersection.Operations.Intersection
public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# `SetIntersection.intersection` is exact

`⋂ (I ++ J) = (⋂ I) ∩ (⋂ J)`: a point lies in every member of the appended list iff it lies in
every member of each. The one guarantee of this class that is an equality; `ZonoBundle`'s
`and_` is this theorem at its members (`ZonoBundle.intersection_exact`).

## Inputs
* `I` – first intersection
* `J` – second intersection

## Hypotheses
* none

## Conclusion
* the appended members denote the intersection of both sets
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type} [ContSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Appending two lists of members denotes exactly the intersection of the two intersections. -/
theorem SetIntersection.intersection_exact (I J : SetIntersection S) :
    ContSet.construct (SetIntersection.intersection I J)
      = ContSet.construct I ∩ ContSet.construct J := by -- --- PROOF ---
  ext x
  simp only [Set.mem_inter_iff, SetIntersection.mem_construct, SetIntersection.intersection,
    List.mem_append]
  exact ⟨fun h => ⟨fun s hs => h s (.inl hs), fun s hs => h s (.inr hs)⟩,
    fun h s hs => hs.elim (h.1 s) (h.2 s)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
