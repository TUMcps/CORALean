import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `ConPolyZono.blkDiag`

`a` copies of a matrix on the diagonal of a block matrix, an entry outside the
blocks being zero. The rows and the columns are both split by
`finProdFinEquiv`, so the block an index belongs to and its position inside that
block are read off the same equivalence.

This is the shape every matrix of [1, Prop. 9] has: its generator exponents, its
constraint generators and its constraint matrix are each the linear
combination's, repeated once per point of the Carathéodory sum, over a fresh
block of factors each time.

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

/-- One copy of `M` per block on the diagonal, and zero off the blocks. -/
def ConPolyZono.blkDiag {β : Type} [Zero β] (a : ℕ) {r c : ℕ} (M : Fin r → Fin c → β) :
    Fin (a * r) → Fin (a * c) → β := fun x y =>
  if (finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm y).1
  then M (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2 else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
