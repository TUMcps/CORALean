import CORALean.ContSet.Capsule.Float.Capsule
import CORALean.ContSet.Capsule.Float.Operations.Origin
import CORALean.ContSet.Capsule.Float.Operations.Empty
import CORALean.ContSet.Capsule.Float.Operations.Center
import CORALean.ContSet.Capsule.Float.Theorems.Convex
import CORALean.ContSet.Capsule.Float.Theorems.IsCompact
import CORALean.ContSet.Capsule.Float.Theorems.CentreMemConstructIff
import CORALean.ContSet.Capsule.Float.Theorems.OriginExact
import CORALean.ContSet.Capsule.Float.Theorems.EmptyExact
import CORALean.ContSet.Capsule.Float.Instances

/-!
# Capsules over a floating-point scalar, collected

The representation in `Capsule`, `origin`, `empty` and `center` in `Operations`, their guarantees
in `Theorems`, and the class instances in `Instances`. The box a capsule is enclosed by, and every
conversion through it, are in `Conversion/Float/Capsule_to_*`.
-/
