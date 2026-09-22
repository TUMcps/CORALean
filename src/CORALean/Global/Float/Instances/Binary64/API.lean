import CORALean.Global.Float.Instances.Binary64.Binary64
import CORALean.Global.Float.Instances.Binary64.Operations
import CORALean.Global.Float.Instances.Binary64.TrustedHardware
import CORALean.Global.Float.Instances.Binary64.Axioms
import CORALean.Global.Float.Instances.Binary64.Theorems.API
import CORALean.Global.Float.Instances.Binary64.Instances

/-!
# Native binary64, collected

What a `Float` denotes in `Binary64`, the directed operations in `Operations`,
what trusting the hardware would mean in `TrustedHardware`, the single axiom
that trusts it in `Axioms`, what follows from it in `Theorems`, and the
`FloatOps` and `SoundFloatArithmetic` instances in `Instances`.

`Axioms` holds the only assumption in the repository, and the only reason to
reach for this backend rather than `Dyadic` is speed.
-/
