import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.Global.Block

/-!
# `ConZonotope.plus`

Generators concatenate exactly and the constraints are padded onto the wider
coefficient space, so only the centre rounds and its `residual` goes into the
box — exactly as for a zonotope, the constraints adding nothing to pay for.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.plus (C₁ C₂ : ConZonotope 𝕋 n) : ConZonotope 𝕋 n where
  h := C₁.h + C₂.h
  c := fun i => addDown (C₁.c i) (C₂.c i)
  G := fun i => Fin.append (C₁.G i) (C₂.G i)
  P := (C₁.P.padLeft C₂.h).and (HPolytope.padRight C₁.h C₂.P)
  E := (C₁.E.plus C₂.E).plus (Zonotope.centerResidual C₁.c C₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
