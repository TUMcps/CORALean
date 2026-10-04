import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestGen

/-!
# `PolyZonotope.polygonRound`, over a floating-point scalar

One round of the refinement CORA's `polygon` runs: every piece the predicate `pick` selects is
split along its longest factor (`splitLongestGen`), the others are kept.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.polygonRound (pick : PolyZonotope 𝕋 2 → Bool) (L : List (PolyZonotope 𝕋 2)) :
    List (PolyZonotope 𝕋 2) :=
  L.flatMap fun q => if pick q then [q.splitLongestGen.1, q.splitLongestGen.2] else [q]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
