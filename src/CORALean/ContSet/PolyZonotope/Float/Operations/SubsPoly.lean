module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.subsPoly`

Output `ii` of `pZin` as a sum of monomials, each stored coefficient a degenerate bracket.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.subsPoly {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu)) (ii : Fin nu) :
    List ((𝕋 × 𝕋) × (Fin pZin.p → ℕ)) :=
  ((pZin.c ii, pZin.c ii), 0) ::
    (List.finRange pZin.h).map fun j => ((pZin.G j ii, pZin.G j ii), fun k => pZin.E k j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
