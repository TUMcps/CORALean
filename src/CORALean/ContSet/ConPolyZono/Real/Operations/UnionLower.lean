module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionSel
public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd
public import CORALean.ContSet.PolyLevelSet.Real.Operations.PadVars
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Switch

@[expose] public section

/-!
# `ConPolyZono.unionLower`

The lower rows of [1, Thm. 1] as a polynomial level set on the union's factors: the operands'
own systems on their own factors (`PolyLevelSet.cartProd`), the two fresh factors after them
(`PolyLevelSet.padVars`), and each row's right-hand side switched by the selector factor `α₁`
(`PolyLevelSet.switch`), at `(1 + α₁) / 2` for the first operand and `(1 - α₁) / 2` for the
second, so that a row binds on its own branch and loses its right-hand side on the other. That is
CORA's `@conPolyZono/or`, `[blkdiag(A₁, A₂), [-b₁; b₂] / 2]` over `b / 2`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p₁ p₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both operands' rows, switched by the selector factor. -/
noncomputable def ConPolyZono.unionLower (P₁ : PolyLevelSet p₁) (P₂ : PolyLevelSet p₂) :
    PolyLevelSet (p₁ + p₂ + 2) :=
  ((P₁.cartProd P₂).padVars 2).switch (ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1)
    (Fin.append (fun _ => true) fun _ => false)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
