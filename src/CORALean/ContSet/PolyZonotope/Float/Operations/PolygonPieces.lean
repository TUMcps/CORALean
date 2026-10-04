import CORALean.ContSet.PolyZonotope.Float.Operations.PolygonRound

/-!
# `PolyZonotope.polygonPieces`, over a floating-point scalar

The pieces after `splits` rounds of refinement; `pick i` chooses which pieces round `i` splits.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.polygonPieces (pZ : PolyZonotope 𝕋 2) (splits : ℕ)
    (pick : ℕ → PolyZonotope 𝕋 2 → Bool) : List (PolyZonotope 𝕋 2) :=
  (List.range splits).foldl (fun L i => PolyZonotope.polygonRound (pick i) L) [pZ]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
