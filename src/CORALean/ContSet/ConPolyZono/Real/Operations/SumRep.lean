import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A sum over replicated indices, block by block

`finProdFinEquiv` turns a sum over `Fin (a * r)` into a sum over the blocks of
a sum inside each, which is the form every constraint row and every generator
block of [1, Prop. 9] is read in.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A sum over `a` blocks of `r`, as a sum of sums. -/
theorem ConPolyZono.sum_rep {M : Type} [AddCommMonoid M] {a r : ℕ} (F : Fin (a * r) → M) :
    ∑ x, F x = ∑ j : Fin a, ∑ k : Fin r, F (finProdFinEquiv (j, k)) := by
  rw [← Equiv.sum_comp finProdFinEquiv F, Fintype.sum_prod_type]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
