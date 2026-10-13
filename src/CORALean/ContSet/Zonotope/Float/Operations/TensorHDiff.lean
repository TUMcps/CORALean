module

public import CORALean.ContSet.Zonotope.Float.Operations.TensorHDown
public import CORALean.ContSet.Zonotope.Float.Operations.TensorHUp

@[expose] public section

/-!
# `Zonotope.tensorHDiff`

How far a stored column of `tensorMultiplication` can be from the exact one: the gap between its two
roundings, which a coefficient in `[-1, 1]` then spreads either way.
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

def Zonotope.tensorHDiff (M : Zonotope.Tensor3 𝕋 n) (Z : Zonotope (Vec 𝕋 n))
    (L : Real.Zonotope.TensorLists Z.h) : Fin n → Fin L.C → 𝕋 :=
  fun iDim cInd => subUp (Zonotope.tensorHUp M Z L iDim cInd) (Zonotope.tensorHDown M Z L iDim cInd)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
