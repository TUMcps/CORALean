module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsPow
public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsPoly

@[expose] public section

/-!
# `PolyZonotope.subsXprod`

CORA's `Xprod` of generator `i`: what its monomial in the replaced factors becomes, the product
over the outputs `ii` of the `e`-th power of output `ii`'s polynomial, `e` the exponent of factor
`idu ii` in the generator.
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

def PolyZonotope.subsXprod (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) (i : Fin pZ.h) : List ((𝕋 × 𝕋) × (Fin pZin.p → ℕ)) :=
  (List.finRange nu).foldl
    (fun acc ii => PolyZonotope.subsMul acc
      (PolyZonotope.subsPow (pZin.subsPoly ii) (pZ.E (idu ii) i)))
    [((one, one), 0)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
