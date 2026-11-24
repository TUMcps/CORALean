module

public import CORALean.ContSet.Taylm.Float.Operations.ConstSparse

@[expose] public section

/-!
# `Taylm.fromRange`

A model with no dependency on its variables that holds the box `[lo, hi]`, as CORA.cpp's
`Taylm::from_range` builds it: the midpoint `(lo + hi) / 2` as the constant (`Taylm.constSparse`)
and the half-width `(hi - lo) / 2` as the remainder `[-w, w]`. The sum rounded up for the midpoint;
what its rounding moves the midpoint by, half the gap of the two roundings, goes to the error box,
which is zero at round to nearest.

## Inputs
* `n` – number of variables
* `lo` – lower end of the box
* `hi` – upper end of the box
* `N` – the order `times` truncates to

## Output
* Taylor model of every number of the box
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

def Taylm.fromRange (n : ℕ) (lo hi : 𝕋) (N : ℕ) : Taylm 𝕋 n :=
  let mid := half (addUp lo hi)                                -- CORA.cpp's 0.5 * (lo + hi)
  let w := half (subUp hi lo)                                  -- the half-width, rounded up
  let g := half (subUp (addUp lo hi) (addDown lo hi))          -- the midpoint's rounding
  { Taylm.constSparse n mid N with
    rem := ⟨neg w, w⟩
    I_error := ⟨neg g, g⟩ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
