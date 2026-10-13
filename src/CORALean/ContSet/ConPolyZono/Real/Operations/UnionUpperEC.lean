import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCol
import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

/-!
# `ConPolyZono.unionUpperEC`

The monomials the two selector rows of [1, Thm. 1] are read against: the single
column `α₁α₂`, then `unionConCol`'s eight groups, transposed into the matrix the
representation stores. Both rows read the same factors, which is why this is
`appendE` and not `plusE`.

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

/-- The selector rows' exponent matrix. -/
def ConPolyZono.unionUpperEC (p₁ p₂ : ℕ) : Fin (p₁ + p₂ + 2) →
    Fin (1 + (2 + (p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂))))) → ℕ :=
  ConPolyZono.appendE
    (fun k _ => ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1 k
      + ConPolyZono.unitCol (Fin.natAdd (p₁ + p₂) 1) 1 k)
    (fun k l => ConPolyZono.unionConCol p₁ p₂ l k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
