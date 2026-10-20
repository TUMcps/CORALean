module

public import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSel
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `ConPolyZono.unionE`

The generator exponent matrix of [1, Thm. 1]: one column `α₁` for the generator
that moves the center to one operand or the other, then the two operands' own
exponent matrices block-diagonally, widened by the two fresh factors.

The `α₂` row is zero throughout — `α₂` exists only to pin `α₁`'s sign — which is
why the fresh factors enter here through `padE` and not otherwise.

## Inputs
* `p₁` – factors of first operand
* `h₁` – generators of first
* `p₂` – factors of second operand
* `h₂` – generators of second
* `E₁` – first exponent matrix
* `E₂` – second exponent matrix

## Output
* exponent matrix of the union

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

/-- One selector column, then each operand's generators over its own factors. -/
def ConPolyZono.unionE {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) : Fin (p₁ + p₂ + 2) → Fin (1 + (h₁ + h₂)) → ℕ :=
  ConPolyZono.appendE (fun k _ => ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1 k)
    (ConPolyZono.padE (PolyZonotope.plusE E₁ E₂) 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
