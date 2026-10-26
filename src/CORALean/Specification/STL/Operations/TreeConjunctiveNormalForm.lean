module

public import CORALean.Specification.STL.Operations.TreeCnfLoop
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# Conjunctive normal form

`@stl/conjunctiveNormalForm.m`: the negation normal form (unless the flag `nnf` says the argument
is one), then the rewrite loop of `STL.Tree.cnfLoop`. The negation normal form is the corrected
one
(`STL.Tree.negationNormalForm`), since the printed one changes the meaning of the formula.

## Inputs
* `φ` – formula
* `nnf` – formula is in negation normal form

## Output
* the formula in conjunctive normal form
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {τ κ : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conjunctiveNormalForm(obj,nnf)`. -/
def STL.Tree.conjunctiveNormalForm (φ : STL.Tree τ κ n) (nnf : Bool := false) : STL.Tree τ κ n :=
  let obj := if nnf then φ else φ.negationNormalForm
  obj.cnfLoop

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
