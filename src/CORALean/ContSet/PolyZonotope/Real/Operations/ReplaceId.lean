module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.replaceId`

CORA's `@polyZonotope/replaceId`: identifiers are renamed, and two factors that receive the same
identifier become one factor, their exponent rows added. An identifier is an index of `Fin p` here
(factor identity is positional, as in `exactPlus`), so the renaming is a map `f : Fin p → Fin p'`
sending each factor to its new identifier, and the new exponent row of an identifier is the sum of
the old rows of the factors sent to it. CORA's replacement of a subset of the identifiers is `f`
the identity elsewhere. The generators, the center and the independent block are untouched.

## Inputs
* `pZ` – polynomial zonotope
* `p'` – new factor count
* `f` – map from old to new factors

## Output
* polynomial zonotope with factors identified along the map
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors renamed by `f`, the exponent rows of factors with a common new name added. -/
def PolyZonotope.replaceId (pZ : PolyZonotope α) {p' : ℕ} (f : Fin pZ.p → Fin p') :
    PolyZonotope α where
  p := p'
  h := pZ.h
  q := pZ.q
  c := pZ.c
  G := pZ.G
  E := fun k' i => ∑ k ∈ Finset.univ.filter (fun k => f k = k'), pZ.E k i
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
