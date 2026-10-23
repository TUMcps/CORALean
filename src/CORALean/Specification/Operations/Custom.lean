module

public import CORALean.Specification.Specification

@[expose] public section

/-!
# `Specification.custom`

CORA's `'custom'` specification: a predicate on the whole set, proved hereditary under `⊆` and
closed under the unions `holds_iUnion` needs, which makes it exactly a safe set.

## Inputs
* `p` – predicate on sets of points

## Hypotheses
* `_mono` – `p` holds of every subset of a set it holds of
* `_iUnionClosed` – `p` holds of the union of sets it holds of

## Output
* the safe set that is the union of all sets the predicate holds of

-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `'custom'`: a predicate on the whole set, proved hereditary under
`⊆` (`mono`) and closed under the unions `holds_iUnion` needs
(`iUnionClosed`) — which makes it exactly a safe set, per `holds_custom_iff`. -/
def Specification.custom (p : Set α → Prop)
    (_mono : ∀ {X O : Set α}, X ⊆ O → p O → p X)
    (_iUnionClosed : ∀ {ι : Type} {X : ι → Set α}, (∀ i, p (X i)) → p (⋃ i, X i)) :
    Specification (Set α) :=
  Specification.safeSet (⋃ h : {S : Set α // p S}, h.1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
