import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConPolyZono.Real.Operations.BlkDiag

/-!
# `ConPolyZono.blkDiag`

`a` copies of a matrix on the diagonal of a block matrix, as [1, Prop. 9] lays out
every matrix of the convex hull, an entry outside the blocks being `zero`. Entries are copied,
so nothing here rounds.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One copy of `M` per block on the diagonal, and `zero` off the blocks. -/
def ConPolyZono.blkDiag (a : ℕ) {r c : ℕ} (M : Fin r → Fin c → 𝕋) :
    Fin (a * r) → Fin (a * c) → 𝕋 := fun x y =>
  if (finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm y).1
  then M (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2 else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
