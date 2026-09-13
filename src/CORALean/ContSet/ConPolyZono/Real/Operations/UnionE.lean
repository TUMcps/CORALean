import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSel
import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

/-!
# `ConPolyZono.unionE`

The generator exponent matrix of [1, Thm. 1]: one column `α₁` for the generator
that moves the centre to one operand or the other, then the two operands' own
exponent matrices block-diagonally, widened by the two fresh factors.

The `α₂` row is zero throughout — `α₂` exists only to pin `α₁`'s sign — which is
why the fresh factors enter here through `padE` and not otherwise.

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

/-- One selector column, then each operand's generators over its own factors. -/
def ConPolyZono.unionE {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) : Fin (p₁ + p₂ + 2) → Fin (1 + (h₁ + h₂)) → ℕ :=
  ConPolyZono.appendE (fun k _ => ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1 k)
    (ConPolyZono.padE (PolyZonotope.plusE E₁ E₂) 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
