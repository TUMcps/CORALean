module

public import CORALean.ContSet.HPolytope.Float.Definitions.API
public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.API
public import CORALean.ContSet.HPolytope.Float.Theorems.API
public import CORALean.ContSet.HPolytope.Float.Instances

/-!
# Halfspace descriptions over a floating-point scalar, collected

The exact layer's rows, a slack per inequality row and per equality row, and the error box every
float representation carries. An operation that rounds a right-hand side keeps the bound and writes
the rounding into the row's slack (`setRhs`, #218), so an equality that must be rounded stays an
equality, a slab as wide as its slack; the box is moved into the slacks where rows are stacked
(`boxToSlack`), and the box and the slacks into the rows (`absorbRounding`) where an operation
reads them.
-/
