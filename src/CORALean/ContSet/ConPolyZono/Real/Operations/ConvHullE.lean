module

public import CORALean.ContSet.ConPolyZono.Real.Operations.BlkDiag
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol

@[expose] public section

/-!
# `ConPolyZono.convHullE`

The generator exponent matrix of [1, Prop. 9]: `a` columns carrying the fresh
weight factors alone, then the linear combination's exponent matrix twice over,
block-diagonally — once as it stands and once multiplied by its copy's weight.

A copy's generator columns therefore come in pairs, `μ` and `λ μ`, which is what
lets the sum be read back as `∑ (1 + λ) (c + ∑ μ G)`: a weighted sum of points
of the combination, with the weights free but for the row that fixes their sum.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Weight columns, then the copies' exponents plain and weighted. -/
def ConPolyZono.convHullE (a : ℕ) {p h : ℕ} (E : Fin p → Fin h → ℕ) :
    Fin (a * p + a) → Fin (a + (a * h + a * h)) → ℕ :=
  Fin.append
    (fun x => Fin.append (fun _ => 0)
      (Fin.append (ConPolyZono.blkDiag a E x) (ConPolyZono.blkDiag a E x)))
    (fun j => Fin.append (ConPolyZono.unitCol j 1)
      (Fin.append (fun _ => 0) (fun y => ConPolyZono.unitCol j 1 (finProdFinEquiv.symm y).1)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
