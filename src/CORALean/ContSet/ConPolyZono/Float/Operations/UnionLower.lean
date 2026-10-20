module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSel
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Float.Operations.PadVars
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Switch

@[expose] public section

/-!
# `ConPolyZono.unionLower` over a floating-point scalar

`Real.ConPolyZono.unionLower` at the stored floats, from the same operations: the operands' rows
on their own factors (`PolyLevelSet.cartProd`), the two fresh factors (`PolyLevelSet.padVars`) and
the right-hand sides switched by the selector factor (`PolyLevelSet.switch`), each row with its
own slack. Halving and negating are exact, so the switch costs no slack.

## Inputs
* `P₁` – constraint of first operand
* `P₂` – constraint of second operand

## Output
* both constraints switched by the selector factor
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {p₁ p₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both operands' rows, switched by the selector factor, whose box is the unit box, each row with
its slack. -/
def ConPolyZono.unionLower (P₁ : PolyLevelSet 𝕋 p₁) (P₂ : PolyLevelSet 𝕋 p₂) :
    PolyLevelSet 𝕋 (p₁ + p₂ + 2) :=
  ((P₁.cartProd P₂).padVars (Interval.unit 2)).switch
    (Real.ConPolyZono.unitCol (Real.ConPolyZono.unionSel p₁ p₂) 1)
    (Fin.append (fun _ => true) fun _ => false)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
