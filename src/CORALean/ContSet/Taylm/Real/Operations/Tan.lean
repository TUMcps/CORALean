module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Mag
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.tan`

CORA's `tan`: the expansion at the constant part. `tan' = 1 + tan²`, so `tan⁽ᴺ⁺¹⁾` is a
polynomial in `tan`, bounded by `odePoly (1 + X²) (N+1)` at `tan` of the magnitude, which is
finite below `π/2`, the domain `TanOuter` assumes.

## Inputs
* `T` – Taylor model

## Output
* Taylor model of tangent of the argument
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.tan (T : Taylm n) : Taylm n :=
  T.taylor Real.tan T.constCoef
    ((odePoly (1 + Polynomial.X ^ 2) (T.maxOrder + 1)).eval (Real.tan T.mag))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
