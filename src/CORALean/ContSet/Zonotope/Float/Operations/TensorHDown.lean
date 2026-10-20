module

public import CORALean.Global.Tensor
public import CORALean.ContSet.Zonotope.Float.Operations.CubContractDown
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Real.Operations.TensorLists

@[expose] public section

/-!
# `Zonotope.tensorHDown`

The generators of `tensorMultiplication` on the stored floats, rounded down: column `cInd` of `H`
is the sum of `tildeH`, the product of three generators through `M`, over the permutations `p` that
`map` sends to `cInd`. The product is `cubContractDown` with the tensor's slices `M iDim ind1` as
the matrices.

## Inputs
* `M` – third-order tensor
* `Z` – zonotope
* `L` – permutation lists

## Output
* tensor generator columns, rounded down
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

def Zonotope.tensorHDown (M : Tensor3 𝕋 n) (Z : Zonotope (Vec 𝕋 n))
    (L : Real.Zonotope.TensorLists Z.h) : Fin n → Fin L.C → 𝕋 :=
  fun iDim cInd =>
    -- `tildeH` of each permutation, those mapped to `cInd` summed
    sumDown fun p : Fin L.P =>
      if L.map p = cInd then
        Zonotope.cubContractDown M (Z.G (L.perm p 0)) (Z.G (L.perm p 1)) (Z.G (L.perm p 2)) iDim
      else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
