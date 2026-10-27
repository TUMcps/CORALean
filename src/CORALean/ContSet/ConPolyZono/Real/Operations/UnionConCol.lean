module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionWithSel
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionCrossCol

@[expose] public section

/-!
# `ConPolyZono.unionConCol`

The exponent columns of [1, Thm. 1]'s selector constraint, read column by column:
`α₁`, `α₂`, then each operand's squares, each of those times `α₁`, then the cross
terms and each of those times `α₁`. Eight groups, `2 + 2p₁ + 2p₂ + 2p₁p₂` columns.

Given as a map from column index to column rather than as the transposed matrix
the representation stores, since every group is defined by what its column *is*;
`unionConR` is this read the other way round.

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand

## Output
* monomials of the selector constraint

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The monomials of the selector constraint, one per column. Not the constraint's work (data): the
monomials of [1, Thm. 1]'s selector polynomial, a fixed row of the union, stored as the
`PolyLevelSet` `unionConRow`. -/
def ConPolyZono.unionConCol (p₁ p₂ : ℕ) :
    Fin (2 + (p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂)))) → Fin (p₁ + p₂ + 2) → ℕ :=
  Fin.append
    ![ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1,
      ConPolyZono.unitCol (Fin.natAdd (p₁ + p₂) 1) 1]
    (Fin.append
      (Fin.append (fun j => ConPolyZono.unitCol (Fin.castAdd 2 (Fin.castAdd p₂ j)) 2)
        (fun j => ConPolyZono.unionWithSel p₁ p₂
          (ConPolyZono.unitCol (Fin.castAdd 2 (Fin.castAdd p₂ j)) 2)))
      (Fin.append
        (Fin.append (fun k => ConPolyZono.unitCol (Fin.castAdd 2 (Fin.natAdd p₁ k)) 2)
          (fun k => ConPolyZono.unionWithSel p₁ p₂
            (ConPolyZono.unitCol (Fin.castAdd 2 (Fin.natAdd p₁ k)) 2)))
        (Fin.append (ConPolyZono.unionCrossCol p₁ p₂)
          (fun l => ConPolyZono.unionWithSel p₁ p₂ (ConPolyZono.unionCrossCol p₁ p₂ l)))))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
