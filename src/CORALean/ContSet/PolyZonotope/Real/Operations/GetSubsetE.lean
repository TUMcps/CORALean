module

public import CORALean.ContSet.PolyZonotope.Real.Operations.MaxExp
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The exponent matrix of `getSubset`

Substituting `αₖ ↦ cen + rad·βₖ` and expanding turns one column of degree `e` in that factor
into `e + 1` columns, of degrees `0 … e` in the new factor and unchanged in every other. The
columns are laid out `d + 1` to an original one, `d` the largest exponent the factor carries,
and `finProdFinEquiv` matches the flat index to the pair, as `bilinE` does. Padding to a
uniform `d + 1` keeps the index a product type; the surplus columns are the ones `getSubsetG`
gives the coefficient `Nat.choose e j = 0`.

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor index

## Output
* exponent matrix of the restricted set
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The substituted factor's exponent is the column's second index; every other
factor keeps the exponent of the column this one expands. -/
def PolyZonotope.getSubsetE (pZ : PolyZonotope α) (k : Fin pZ.p) :
    Fin pZ.p → Fin (pZ.h * (pZ.maxExp k + 1)) → ℕ :=
  fun k' l => if k' = k then ((finProdFinEquiv.symm l).2 : ℕ)
    else pZ.E k' (finProdFinEquiv.symm l).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
