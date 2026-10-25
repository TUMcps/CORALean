module

public import CORALean.Global.Float.Instances.Flint.Definitions.Axioms
public import CORALean.Global.Float.Instances.Flint.Definitions.IsTrustedFlint

/-!
# What trusting FLINT means, collected

`IsTrustedFlint` is one property with six conjuncts, the directed laws of the six
operations FLINT computes; `Axioms` assumes it once. The exact operations are
pure Lean and proved in `Theorems/`, so this is all the backend trusts.
-/
