module

public import CORALean.ContSet.Zonotope.Float.Operations.CubContractUp
public import CORALean.ContSet.Zonotope.Float.Operations.Tensor3
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Real.Operations.TensorLists

@[expose] public section

/-!
# `Zonotope.tensorHUp`

`Zonotope.tensorHDown` rounded up, for the gap that the box is charged.
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

def Zonotope.tensorHUp (M : Zonotope.Tensor3 𝕋 n) (Z : Zonotope (Vec 𝕋 n))
    (L : Real.Zonotope.TensorLists Z.h) : Fin n → Fin L.C → 𝕋 :=
  fun iDim cInd =>
    sumUp fun p : Fin L.P =>
      if L.map p = cInd then
        Zonotope.cubContractUp M (Z.G (L.perm p 0)) (Z.G (L.perm p 1)) (Z.G (L.perm p 2)) iDim
      else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
