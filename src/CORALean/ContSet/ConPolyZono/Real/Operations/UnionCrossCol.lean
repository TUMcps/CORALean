import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `ConPolyZono.unionCrossCol`

The cross terms of [1, Thm. 1]'s selector constraint: one square from each
operand's factor block, `αⱼ² αₖ²`, indexed by the pair `(j,k)` that
`finProdFinEquiv` reads off a single column index.

There are `p₁ p₂` of them, and they are what makes the constraint's column count
quadratic rather than linear in the operands' factor counts.

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

/-- The exponent column `αⱼ² αₖ²`, one factor squared from each operand. -/
def ConPolyZono.unionCrossCol (p₁ p₂ : ℕ) (l : Fin (p₁ * p₂)) : Fin (p₁ + p₂ + 2) → ℕ :=
  fun k => ConPolyZono.unitCol
      (Fin.castAdd 2 (Fin.castAdd p₂ (finProdFinEquiv.symm l).1)) 2 k
    + ConPolyZono.unitCol (Fin.castAdd 2 (Fin.natAdd p₁ (finProdFinEquiv.symm l).2)) 2 k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
