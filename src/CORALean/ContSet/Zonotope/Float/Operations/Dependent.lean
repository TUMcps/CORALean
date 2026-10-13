import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound

/-!
# `Zonotope.dependent`

The error box made into generators: one fresh generator per coordinate, as long as the box's larger
endpoint (`errorBound`, which rounds nothing). A cubic map is not additive, so a nominal part and a
box cannot travel through it separately; emptying the box first is what `cubMap` needs, as for
`ConZonotope.dependent` and `PolyZonotope.dependent`.
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

def Zonotope.dependent (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := Z.h + n
  c := Z.c
  G := Fin.append Z.G (diagonalBlock (PolyZonotope.errorBound Z.E))
  E := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
