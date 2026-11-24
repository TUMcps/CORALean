module

public import CORALean.ContSet.Taylm.Float.Operations.Basic

@[expose] public section

/-!
# `Taylm.constSparse`

A constant Taylor model as CORA.cpp's `Taylm::constant` builds it: the number as the term of the
zero exponents, no term at all if the number is zero (its ordered map stores only nonzero
coefficients), and a zero remainder.

## Inputs
* `n` – number of variables
* `c` – the constant
* `N` – the order `times` truncates to

## Output
* Taylor model of the constant
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.constSparse (n : ℕ) (c : 𝕋) (N : ℕ) : Taylm 𝕋 n :=
  -- `le` both ways certifies a zero, which CORA.cpp's map leaves out
  if le c zero && le zero c then ⟨[], ⟨zero, zero⟩, ⟨zero, zero⟩, N⟩
  else Taylm.const n c N

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
