module

public import CORALean.Specification.Specification
public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# `HoldsAll` over safe sets alone is `Holds` on their `SetIntersection`

`HoldsAll` checks a list of specifications one at a time, any mix of kinds;
restricted to safe sets (or invariants, checked identically) it is exactly
`X` inside their `SetIntersection`, the safe-set spec CORA names nothing but
this tree already has a representation of. Stated for `safeSet`, and does
not replace `HoldsAll`, which stays what a heterogeneous list still needs.

## Inputs
* `sets` – list of sets
* `X` – set of points

## Hypotheses
* none

## Conclusion
* all listed safe sets hold iff the safe set of their intersection holds
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {ContSet α : Type} [CORALean.ContSet ContSet α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `HoldsAll` over a list of safe sets, read as one safe set on their
`SetIntersection`: `X` inside every listed set iff `X` inside all of them. -/
theorem Specification.holdsAll_safeSet_iff_setIntersection_holds
    (sets : List ContSet) (X : Set α) : -- --- CONCL ---
    Specification.HoldsAll (sets.map Specification.safeSet) X ↔
      (Specification.safeSet (⟨sets⟩ : SetIntersection ContSet) :
        Specification (SetIntersection ContSet)).Holds X := by -- --- PROOF ---
  constructor
  · intro h
    exact Set.subset_iInter₂ fun s hs => h (Specification.safeSet s) (List.mem_map_of_mem hs)
  · intro h spec hspec
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hspec
    exact h.trans (Set.iInter₂_subset s hs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
