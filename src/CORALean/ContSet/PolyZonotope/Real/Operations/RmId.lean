module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# `PolyZonotope.rmId`

CORA's `@polyZonotope/rmId`: delete the exponent rows, and the identifiers, of the listed
factors. A deleted factor no longer scales anything, which is the same as pinning it at `1`
(`rmId_construct`), so the result is the subset of the set where those factors are `1`.
CORA then runs `removeRedundantExponents`, merging equal exponent columns; the denoted set is
the same and the merge is left out.

Factor identity being positional, the identifiers become a `Finset` of row indices, and the
rows that stay are read off in order by `orderIsoOfFin`.

## Inputs
* `pZ` – polynomial zonotope
* `S` – factors to remove

## Output
* polynomial zonotope without those factors
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pZ` without the exponent rows of the factors in `S`. -/
def PolyZonotope.rmId (pZ : PolyZonotope α) (S : Finset (Fin pZ.p)) : PolyZonotope α where
  p := Sᶜ.card
  h := pZ.h
  q := pZ.q
  c := pZ.c
  G := pZ.G
  E := fun k => pZ.E (Sᶜ.orderIsoOfFin rfl k).1
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
