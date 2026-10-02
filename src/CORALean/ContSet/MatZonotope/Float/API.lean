import CORALean.ContSet.MatZonotope.Float.MatZonotope
import CORALean.ContSet.MatZonotope.Float.Operations.API
import CORALean.ContSet.MatZonotope.Float.Theorems.API
import CORALean.ContSet.MatZonotope.Float.Instances

/-!
# Matrix zonotopes over a floating-point scalar, collected

The representation and what it denotes in `MatZonotope`, the operations in `Operations`,
their guarantees in `Theorems`, and the `ContSet` instance in `Instances`. Its action on a
float zonotope, `Zonotope.mtimesMatZonotope`, sits with `Zonotope`, and its interval hull
under `Conversion/Float`.
-/
