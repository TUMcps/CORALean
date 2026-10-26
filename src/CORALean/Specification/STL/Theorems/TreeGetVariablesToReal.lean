module

public import CORALean.Specification.STL.Operations.ExprMap
public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.ExprVariables
public import CORALean.Specification.STL.Operations.TreeGetVariables
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# `getVariables` of a float syntax tree, read as reals

The variables a formula mentions do not depend on its times or numbers, so the tree and its reading
mention the same ones.

## Inputs
* `φ` – formula

## Hypotheses
* none

## Conclusion
* the variables of the reading are those of the tree
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {τ τ' κ κ' : Type} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `variables` of an expression and mapping its numbers. -/
private theorem aux_variables_map (g : κ → κ') (e : STL.Expr κ n) :
    (e.map g).variables = e.variables := by
  induction e <;> simp_all [STL.Expr.variables, STL.Expr.map]

/-- `getVariables` and mapping the times and numbers. -/
private theorem aux_getVariables_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) :
    (φ.map f g).getVariables = φ.getVariables := by
  induction φ <;> simp_all [STL.Tree.getVariables, STL.Tree.map, aux_variables_map]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.getVariables_toReal (φ : STL.Tree 𝕋 𝕋 n) :
    φ.toReal.getVariables = φ.getVariables :=
  aux_getVariables_map _ _ φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
