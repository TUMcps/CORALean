import CORALean.ContSet.PolyZonotope.Float.Operations.SubsGDown

/-!
# `PolyZonotope.subsGDiff`

What the rounded-down generators of `subs` cost: the rounded-up entry minus the rounded-down one,
rounded up. Both bracket the exact entry.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.subsGDiff (pZ : PolyZonotope (Vec 𝕋 n)) {nu : ℕ} (pZin : PolyZonotope (Vec 𝕋 nu))
    (idu : Fin nu → Fin pZ.p) : Mat 𝕋 n (pZ.subsTerms pZin idu).length := fun r l =>
  let t := (pZ.subsTerms pZin idu).get l
  subUp (Interval.mulHi t.2.1.1 t.2.1.2 (pZ.G t.1 r) (pZ.G t.1 r)) (pZ.subsGDown pZin idu r l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
