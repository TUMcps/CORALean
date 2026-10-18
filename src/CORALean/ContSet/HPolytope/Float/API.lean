module

public import CORALean.ContSet.HPolytope.Float.Definitions.API
public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.API
public import CORALean.ContSet.HPolytope.Float.Theorems.API
public import CORALean.ContSet.HPolytope.Float.Instances

/-!
# Halfspace descriptions over a floating-point scalar, collected

The exact layer's rows, a slack per inequality row and per equality row, and the error box every
float representation carries. An equality that must be rounded stays an equality where a
certified right inverse moves every point onto the stored hyperplane, the step paid into the box
(`anchorEqs`), and is written as two inequalities otherwise; the box and the slacks are moved
into the rows (`absorbRounding`) where an operation reads them.
-/
