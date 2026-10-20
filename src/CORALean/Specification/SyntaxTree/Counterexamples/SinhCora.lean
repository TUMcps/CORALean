module

public import CORALean.ContSet.Interval.Real.Operations.Sinh
public import CORALean.Specification.SyntaxTree.Counterexamples.FunHanSinhCora
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `sinh`, as printed

`sinh(obj)` of `syntaxTree.m` with its `funHan` as printed, `funHanSinhCora`, which is not sound
(see
`SyntaxTree.sinhCora_counterexample`). `SyntaxTree.sinh` is the node with the corrected `funHan`.

## Inputs
* `obj` – operand tree

## Output
* the printed sinh node
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sinh(obj)` as printed: the node `'sinh'` with `funHan = aux_sinh_` of `syntaxTree.m`. -/
noncomputable def SyntaxTree.sinhCora (obj : SyntaxTree n) : SyntaxTree n :=
  .unary .sinh (Real.Interval.sinh obj.value) funHanSinhCora obj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
