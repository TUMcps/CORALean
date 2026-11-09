module

public import CORALean.HybridDynamics.Operations.GuardGroups

@[expose] public section

/-!
# `Location.guardIntersectGrouped`

CORA's `@location/guardIntersect.m` around its methods: the hits are grouped into crossings
(`Location.guardGroups`), a method encloses the sets of each crossing, and a crossing whose
enclosure is empty is dropped (`aux_removeEmptySets`). The method is a parameter: any of
`guardIntersectFloat`, `guardIntersectZonoGirardFloat`, `guardIntersectNondetFloat` or
`guardIntersectPolytopeFloat` with its basis and guard, each as a function of the transition and
of the sets of the crossing.

## Inputs
* `enclose` – the method: transition and sets of one crossing to an enclosure, none if empty
* `sets` – reach sets, indexed as the hits are
* `hits` – `(transition, set index)` pairs

## Output
* per crossing the transition, the first and the last set index, and the enclosure
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {Z E : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The non-empty enclosures of the crossings of `hits`, with the transition and the first and last
set index of each (`guardIntersect`'s `Rguard`, `actGuards`, `minInd`, `maxInd`). -/
def Location.guardIntersectGrouped (enclose : ℕ → List Z → Option E) (sets : List Z)
    (hits : List (ℕ × ℕ)) : List (ℕ × ℕ × ℕ × E) :=
  (Location.guardGroups hits).filterMap fun grp =>
    match grp.2, enclose grp.1 (grp.2.filterMap fun j => sets[j]?) with
    | j₀ :: js, some R => some (grp.1, j₀, (j₀ :: js).getLast (List.cons_ne_nil _ _), R)
    | _, _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
