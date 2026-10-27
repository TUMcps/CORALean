module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSelRow
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet

@[expose] public section

/-!
# `ConPolyZono.unionSelRow` over a floating-point scalar

`Real.ConPolyZono.unionSelRow` at the stored floats: `α₁α₂ = 1` of [1, Thm. 1], its coefficient
and right-hand side `one`, stored exactly, so its slack is `zero`.

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand

## Output
* selector equation on the union's factors

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

/-- `α₁α₂ = 1`, on the union's factors and their unit box, with no slack. -/
def ConPolyZono.unionSelRow (p₁ p₂ : ℕ) : PolyLevelSet 𝕋 (p₁ + p₂ + 2) :=
  ⟨1, 1, fun _ _ => one, (Real.ConPolyZono.unionSelRow p₁ p₂).R, fun _ => one, fun _ => zero,
    fun _ => .eq, Interval.unit _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
