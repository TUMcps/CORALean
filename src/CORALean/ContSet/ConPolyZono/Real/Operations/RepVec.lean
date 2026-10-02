import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `ConPolyZono.repVec`

The same entries in every block: `a` copies of a vector side by side, read
through `finProdFinEquiv` exactly as `blkDiag`'s blocks are. It is what carries
the centre, the generators and the constraint bound of [1, Prop. 9] into each of
the `a` copies of the linear combination.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a` copies of `v`, an index reading the entry at its position in its block. -/
def ConPolyZono.repVec {β : Type} (a : ℕ) {r : ℕ} (v : Fin r → β) : Fin (a * r) → β :=
  fun x => v (finProdFinEquiv.symm x).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
