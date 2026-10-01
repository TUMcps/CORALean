import CORALean.ContSet.ContSet.Operations.Enlarge
import CORALean.ContSet.ContSet.Operations.Minus
import CORALean.ContSet.ContSet.Operations.MinusFrom
import CORALean.ContSet.ContSet.Operations.SupportBoundSegments
import CORALean.ContSet.ContSet.Operations.Times
import CORALean.ContSet.ContSet.Operations.Uminus
import CORALean.ContSet.ContSet.Operations.Uplus

/-!
# What the set interface computes

`SupportBoundSegments` carries a support-function bound across `segments`, CORA's `linComb`.

The derived methods, written over the classes: `times`, `uminus` through `mtimes`, `uplus` the
identity, `minus` and `minusFrom` through `plus` and `ofPoint`, and `enlarge` through `centre`.
-/
