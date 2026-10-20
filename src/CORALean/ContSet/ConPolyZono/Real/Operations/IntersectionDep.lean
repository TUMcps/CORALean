module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.CartProd
public import CORALean.ContSet.ConPolyZono.Real.Operations.AgreeCons
public import CORALean.ContSet.PolyLevelSet.Real.Operations.And
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.intersectionDep`

Both sets' factors side by side: each set's equations on its own factors
(`PolyLevelSet.cartProd`), and with them the rows pinning the two points together
(`agreeCons`, `PolyLevelSet.andRows`, on the factors' unit box). Exact where both independent
blocks are empty (`intersectionDep_exact`); `intersection` arranges that.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Output
* intersection for dependent-only operands
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact where both independent blocks are empty; `intersection` arranges that. -/
def ConPolyZono.intersectionDep (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) : ConPolyZono (Vec ℝ n) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  qI := 0
  c := cPZ₁.c
  G := Fin.append cPZ₁.G 0
  E := PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.elim0
  cons := (cPZ₁.cons.cartProd cPZ₂.cons).andRows (ConPolyZono.agreeCons cPZ₁ cPZ₂)
  cons_eq := LevelSet.append_op_eq (LevelSet.append_op_eq cPZ₁.cons_eq cPZ₂.cons_eq)
    fun _ => rfl
  cons_dom := Interval.append_eq_unit cPZ₁.cons_dom cPZ₂.cons_dom

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
