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

def PolyZonotope.plus (PZ₁ PZ₂ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n where
  p := PZ₁.p + PZ₂.p
  h := PZ₁.h + PZ₂.h
  q := PZ₁.q + PZ₂.q
  c := fun i => addDown (PZ₁.c i) (PZ₂.c i)
  G := fun i => Fin.append (PZ₁.G i) (PZ₂.G i)
  E := Real.PolyZonotope.plusE PZ₁.E PZ₂.E
  GI := fun i => Fin.append (PZ₁.GI i) (PZ₂.GI i)
  err := (PZ₁.err.plus PZ₂.err).plus (PolyZonotope.centerResidual PZ₁.c PZ₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
