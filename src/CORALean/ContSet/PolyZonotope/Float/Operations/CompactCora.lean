module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Construct
public import CORALean.ContSet.PolyZonotope.Float.Operations.CompactFactors
public import CORALean.ContSet.PolyZonotope.Float.Operations.FoldConstants

@[expose] public section

/-!
# `PolyZonotope.compactCora`

CORA.cpp's `compact` of a polynomial zonotope: the generators with no factor go into the center
(`foldConstants`), the factors no column reads are dropped (`compactFactors`), and the constructor
runs again on the result (`construct`: zero generators dropped, equal columns added in the order of
`order`). `PolyZonotope.compact` merges first and rounds the merge into the error box; here the
merge is the constructor's.

## Inputs
* `order` – the order of the columns, as for `construct`
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope in CORA.cpp's compact form
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.compactCora (order : ℕ → Array (Array ℕ) → Array ℕ)
    (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  (pZ.foldConstants.compactFactors).construct order

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
