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

def ConZonotope.plus (cZ₁ cZ₂ : ConZonotope 𝕋 n) : ConZonotope 𝕋 n where
  h := cZ₁.h + cZ₂.h
  c := fun i => addDown (cZ₁.c i) (cZ₂.c i)
  G := fun i => Fin.append (cZ₁.G i) (cZ₂.G i)
  P := (cZ₁.P.padLeft cZ₂.h).and (HPolytope.padRight cZ₁.h cZ₂.P)
  E := (cZ₁.E.plus cZ₂.E).plus (Zonotope.centerResidual cZ₁.c cZ₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
