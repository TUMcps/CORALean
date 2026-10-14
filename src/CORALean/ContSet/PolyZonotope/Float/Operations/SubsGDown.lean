module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Basic

@[expose] public section

/-!
# `PolyZonotope.subsGDown`

The generators of `PolyZonotope.subs`, rounded down: the term's coefficient bracket times the
original generator's entry, through the directed product.
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

def PolyZonotope.subsGDown (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) : Mat 𝕋 n (pZ.subsTerms pZin idu).length := fun r l =>
  let t := (pZ.subsTerms pZin idu).get l
  Interval.mulLo t.2.1.1 t.2.1.2 (pZ.G t.1 r) (pZ.G t.1 r)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
