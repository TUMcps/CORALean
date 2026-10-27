module

public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConCoef
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConErr
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCol
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet

@[expose] public section

/-!
# `ConPolyZono.unionConRow` over a floating-point scalar

`Real.ConPolyZono.unionConRow` at the stored floats: the selector polynomial of [1, Thm. 1]
`= 0`, its coefficients rounded (`unionConCoef`), the summed gap between their two roundings its
slack (`unionConErr`).

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand

## Output
* selector polynomial constraint on the unit box

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The selector polynomial `= 0`, to within its coefficients' rounding, on the unit box. -/
def ConPolyZono.unionConRow (p₁ p₂ : ℕ) : PolyLevelSet 𝕋 (p₁ + p₂ + 2) :=
  ⟨1, _, fun _ l => ConPolyZono.unionConCoef p₁ p₂ l,
      fun k l => Real.ConPolyZono.unionConCol p₁ p₂ l k,
    fun _ => zero, fun _ => ConPolyZono.unionConErr p₁ p₂, fun _ => .eq, Interval.unit _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
