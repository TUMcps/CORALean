module

public import CORALean.ContSet.Interval.Real.Operations.Tan
public import CORALean.Specification.SyntaxTree.Counterexamples.FunHanTanCora
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `tan`, as printed

`tan(obj)` of `syntaxTree.m` with its `funHan` as printed, `funHanTanCora`, which is not sound (see
`SyntaxTree.tanCora_counterexample`). `SyntaxTree.tan` is the node with the corrected `funHan`.

## Inputs
* `obj` – operand tree

## Output
* the printed tan node
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `tan(obj)` as printed: the node `'tan'` with `funHan = aux_tan_` of `syntaxTree.m`. -/
noncomputable def SyntaxTree.tanCora (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .tan (Real.Interval.tan obj.value) funHanTanCora obj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
