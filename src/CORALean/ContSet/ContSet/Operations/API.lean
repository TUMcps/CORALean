import CORALean.ContSet.ContSet.Operations.Eq
import CORALean.ContSet.ContSet.Operations.Ne
import CORALean.ContSet.ContSet.Operations.Enclose
import CORALean.ContSet.ContSet.Operations.Enlarge
import CORALean.ContSet.ContSet.Operations.EnlargeScalar
import CORALean.ContSet.ContSet.Operations.Minus
import CORALean.ContSet.ContSet.Operations.MinusFromScalar
import CORALean.ContSet.ContSet.Operations.MinusScalar
import CORALean.ContSet.ContSet.Operations.MinusFrom
import CORALean.ContSet.ContSet.Operations.ProjectHighDim
import CORALean.ContSet.ContSet.Operations.Project
import CORALean.ContSet.ContSet.Operations.Decompose
import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplane
import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneFloat
import CORALean.ContSet.ContSet.Operations.SupportBoundSegments
import CORALean.ContSet.ContSet.Operations.Times
import CORALean.ContSet.ContSet.Operations.Uminus
import CORALean.ContSet.ContSet.Operations.Uplus

/-!
# What the set interface computes

`SupportBoundSegments` carries a support-function bound across `segments`, CORA's `linComb`.

The derived methods, written over the classes: `times`, `uminus` through `mtimes`, `uplus` the
identity, `minus` and `minusFrom` through `plus` and `ofPoint`, `enlarge` through `centre`,
`enclose` through `linComb`, `mtimes` and `plus`, `projectHighDim_` through `mtimes` at a selection
matrix, and `projectOnHyperplane` through `mtimes`, `plus` and `ofPoint`.
-/
