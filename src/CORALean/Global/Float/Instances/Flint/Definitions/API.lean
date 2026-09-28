import CORALean.Global.Float.Instances.Flint.Definitions.Axioms
import CORALean.Global.Float.Instances.Flint.Definitions.TrustedFlint

/-!
# What trusting FLINT means, collected

`TrustedFlint` is one property with six conjuncts, the directed laws of the six
operations FLINT computes; `Axioms` assumes it once. The exact operations are
pure Lean and proved in `Theorems/`, so this is all the backend trusts.
-/
