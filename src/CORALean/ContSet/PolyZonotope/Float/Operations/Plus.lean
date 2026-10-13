import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.CenterResidual
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

/-!
# `PolyZonotope.plus`

All three generator blocks concatenate exactly and the exponent matrices go side
by side block-diagonally over ℕ, so only the centre rounds and its `residual`
goes into the box. Both counts stay where they are over ℝ.

The exponent matrix is the exact layer's `plusE`, reused rather than restated:
it is a matrix of naturals and nothing about it rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.plus (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := pZ₁.p + pZ₂.p
  h := pZ₁.h + pZ₂.h
  q := pZ₁.q + pZ₂.q
  c := fun i => addDown (pZ₁.c i) (pZ₂.c i)
  G := Fin.append pZ₁.G pZ₂.G
  E := Real.PolyZonotope.plusE pZ₁.E pZ₂.E
  GI := Fin.append pZ₁.GI pZ₂.GI
  err := (pZ₁.err.plus pZ₂.err).plus (PolyZonotope.centerResidual pZ₁.c pZ₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
