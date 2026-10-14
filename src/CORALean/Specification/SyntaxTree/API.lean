module

public import CORALean.Specification.SyntaxTree.Definitions.API
public import CORALean.Specification.SyntaxTree.Operations.API
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.API
public import CORALean.Specification.SyntaxTree.Counterexamples.API

/-!
# CORA's `syntaxTree`, collected

The expression tree of the forward-backward contractor (`contractForwardBackward`): a variable
leaf, or
an operator node holding the interval that encloses its value over a box and the `funHan` that
narrows
its operand's interval. `Operations` has the constructor of each operator and `backpropagation`;
`Theorems` says what each denotes (`eval_*`), that its interval encloses it (`encloses_*`), that its
`funHan` is sound (`*_sound`), and that `backpropagation` of a sound tree keeps every solution
(`backpropagation_sound`). Three printed `funHan`s are not sound: `sinhCora_counterexample`,
`tanCora_counterexample`, `powerOddCora_counterexample`.

Not here: the display of a tree, matrix-valued operands beyond `sum`, `prod` and `mtimes`, and
negative,
fractional or `NaN` exponents.
-/
