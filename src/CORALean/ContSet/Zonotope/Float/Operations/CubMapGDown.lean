import CORALean.ContSet.Zonotope.Float.Operations.CubFoldDown
import CORALean.ContSet.Zonotope.Real.Operations.CubIdx

/-!
# `Zonotope.cubMapGDown`

The generators of `Zonotope.cubMap` on the stored floats, rounded down, indexed by all ordered
triples (`Real.Zonotope.cubIdx`): `cubFoldDown` at the sorted triples `k ≤ j ≤ c` other than the
centre's `(0, 0, 0)`, zero elsewhere, halved where it is a pure square `(0, j, j)`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.cubMapGDown (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) :
    Fin m → Fin ((Z.h + 1) * (Z.h + 1) * (Z.h + 1)) → 𝕋 :=
  fun i l =>
    let t := Real.Zonotope.cubIdx (Z.h + 1) (Z.h + 1) (Z.h + 1) l
    if t.1.1 ≤ t.1.2 ∧ t.1.2 ≤ t.2 ∧ ¬(t.1.1 = 0 ∧ t.1.2 = 0 ∧ t.2 = 0) then
      (if t.1.1 = 0 ∧ t.1.2 = t.2 then half (Zonotope.cubFoldDown T Z i t.1.1 t.1.2 t.2)
        else Zonotope.cubFoldDown T Z i t.1.1 t.1.2 t.2)
    else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
