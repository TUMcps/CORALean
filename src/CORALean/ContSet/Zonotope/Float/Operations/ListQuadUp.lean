module

public import CORALean.ContSet.Zonotope.Float.Operations.CubContractUp

@[expose] public section

/-!
# `Zonotope.listQuadUp`

CORA's `listQuad{j}(a, b)` of `aux_cubMapSingle`, for extended columns `Zext`, in `𝕋`, rounded up:
the cubic contraction at `(j, a, b)`, plus the one at `(j, b, a)` for `a < b` (the symmetrized
pair), the pure square `a = b` as it is, and `0` below the diagonal.

## Inputs
* `T` – cubic tensor
* `Zext` – extended columns
* `i` – output coordinate
* `j` – first index
* `a` – second index
* `b` – third index

## Output
* symmetrized contraction at the triple, rounded up
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.listQuadUp (T : Fin m → Fin n → Mat 𝕋 n n) (Zext : Fin N → Vec 𝕋 n) (i : Fin m)
    (j a b : Fin N) : 𝕋 :=
  if a < b then addUp (Zonotope.cubContractUp T (Zext j) (Zext a) (Zext b) i)
    (Zonotope.cubContractUp T (Zext j) (Zext b) (Zext a) i)
  else if a = b then Zonotope.cubContractUp T (Zext j) (Zext a) (Zext a) i else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
