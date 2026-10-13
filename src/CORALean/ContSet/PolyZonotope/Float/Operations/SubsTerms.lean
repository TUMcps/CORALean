module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsXprod

@[expose] public section

/-!
# `PolyZonotope.subsTerms`

The generators of the result, as pairs of an original generator and a term.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.subsTerms (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) : List (Fin pZ.h × ((𝕋 × 𝕋) × (Fin pZin.p → ℕ))) :=
  (List.finRange pZ.h).flatMap fun i => (pZ.subsXprod pZin idu i).map fun t => (i, t)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
