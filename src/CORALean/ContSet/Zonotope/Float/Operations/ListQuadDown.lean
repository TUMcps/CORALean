import CORALean.ContSet.Zonotope.Float.Operations.CubContractDown

/-!
# `Zonotope.listQuadDown`

CORA's `listQuad{j}(a, b)` of `aux_cubMapSingle`, for extended columns `Zext`, in `𝕋`, rounded
down: the cubic contraction at `(j, a, b)`, plus the one at `(j, b, a)` for `a < b` (the
symmetrized pair), the pure square `a = b` as it is, and `0` below the diagonal.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.listQuadDown (T : Fin m → Fin n → Mat 𝕋 n n) (Zext : Fin N → Vec 𝕋 n) (i : Fin m)
    (j a b : Fin N) : 𝕋 :=
  if a < b then addDown (Zonotope.cubContractDown T (Zext j) (Zext a) (Zext b) i)
    (Zonotope.cubContractDown T (Zext j) (Zext b) (Zext a) i)
  else if a = b then Zonotope.cubContractDown T (Zext j) (Zext a) (Zext a) i else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
