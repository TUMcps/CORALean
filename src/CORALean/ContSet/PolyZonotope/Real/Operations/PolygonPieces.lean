module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PolygonRound

@[expose] public section

/-!
# `PolyZonotope.polygonPieces`

The pieces `polygon` ends with: `splits` rounds, `pick i` choosing the pieces refined in round
`i`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.polygonPieces (pZ : PolyZonotope (Vec ℝ 2)) (splits : ℕ)
    (pick : ℕ → PolyZonotope (Vec ℝ 2) → Bool) : List (PolyZonotope (Vec ℝ 2)) :=
  (List.range splits).foldl (fun L i => PolyZonotope.polygonRound (pick i) L) [pZ]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
