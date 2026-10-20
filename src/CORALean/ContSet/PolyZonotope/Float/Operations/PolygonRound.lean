module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestGen

@[expose] public section

/-!
# `PolyZonotope.polygonRound`, over a floating-point scalar

One round of the refinement CORA's `polygon` runs: every piece the predicate `pick` selects is
split along its longest factor (`splitLongestGen`), the others are kept.

## Inputs
* `pick` – chooser of the sets to split
* `L` – list of polynomial zonotopes

## Output
* list with the chosen sets split in two
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.polygonRound (pick : PolyZonotope (Vec 𝕋 2) → Bool)
    (L : List (PolyZonotope (Vec 𝕋 2))) :
    List (PolyZonotope (Vec 𝕋 2)) :=
  L.flatMap fun q => if pick q then [q.splitLongestGen.fst, q.splitLongestGen.snd] else [q]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
