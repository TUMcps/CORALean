import CORALean.ContSet.PolyZonotope.Real.Operations.MaxExp
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The dependent generators of `getSubset`

The binomial coefficients of `(cen + rad·βₖ)^e`, each scaling the generator of
the column it expands: term `j` carries `C(e,j)·cenᵉ⁻ʲ·radʲ`. CORA builds the
same numbers by convolving `[rad cen]` with itself `e` times; `Nat.choose` gives
them in closed form, and gives the padding for free — a column past the degree
gets `C(e,j) = 0` and so a zero generator, which `compact` is free to drop.

At `rad = 0` only `j = 0` survives and the coefficient is `cenᵉ`, which is
exactly CORA's separate point branch `aux_getSubsetPoint`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The column's generator, scaled by the binomial coefficient its degree in the
new factor carries. -/
def PolyZonotope.getSubsetG (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ) :
    Fin (pZ.h * (pZ.maxExp k + 1)) → α :=
  fun l => (((pZ.E k (finProdFinEquiv.symm l).1).choose (finProdFinEquiv.symm l).2 : ℝ)
      * cen ^ (pZ.E k (finProdFinEquiv.symm l).1 - ((finProdFinEquiv.symm l).2 : ℕ))
      * rad ^ ((finProdFinEquiv.symm l).2 : ℕ)) • pZ.G (finProdFinEquiv.symm l).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
