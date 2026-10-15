module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound

@[expose] public section

/-!
# `Zonotope.dependent`

The error box made into generators: one fresh generator per coordinate, as long as the box's larger
endpoint (`errorBound`, which rounds nothing). A cubic map is not additive, so a nominal part and a
box cannot travel through it separately; emptying the box first is what `cubMap` needs, as for
`ConZonotope.dependent` and `PolyZonotope.dependent`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.dependent (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := Z.h + n
  c := Z.c
  G := Fin.append Z.G (diagonalBlock (PolyZonotope.errorBound Z.I_error))
  I_error := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
