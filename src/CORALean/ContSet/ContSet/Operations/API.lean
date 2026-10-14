module

public import CORALean.ContSet.ContSet.Operations.Basic
public import CORALean.ContSet.ContSet.Operations.Enclose
public import CORALean.ContSet.ContSet.Operations.Enlarge
public import CORALean.ContSet.ContSet.Operations.EnlargeScalar
public import CORALean.ContSet.ContSet.Operations.IntersectStripSeq
public import CORALean.ContSet.ContSet.Operations.Minus
public import CORALean.ContSet.ContSet.Operations.MinusScalar
public import CORALean.ContSet.ContSet.Operations.ProjectHighDim
public import CORALean.ContSet.ContSet.Operations.Project
public import CORALean.ContSet.ContSet.Operations.Decompose
public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplane
public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneFloat
public import CORALean.ContSet.ContSet.Operations.SupportBoundSetLinComb
public import CORALean.ContSet.ContSet.Operations.Times
public import CORALean.ContSet.ContSet.Operations.Polygon
public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneIntervalFloat

/-!
# What the set interface computes

`SupportBoundSetLinComb` carries a support-function bound across `Set.linComb`, CORA's `linComb`.

The derived methods, written over the classes: `times`, `uminus` through `mtimes`, `uplus` the
identity, `minus` and `minusFrom` through `plus` and `ofPoint`, `enlarge` through `centre`,
`enclose` through `linComb`, `mtimes` and `plus`, `projectHighDim_` through `mtimes` at a selection
matrix, and `projectOnHyperplane` through `mtimes`, `plus` and `ofPoint`.
-/
