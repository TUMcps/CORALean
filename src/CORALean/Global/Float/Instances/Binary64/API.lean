import CORALean.Global.Float.Instances.Binary64.Binary64
import CORALean.Global.Float.Instances.Binary64.Definitions.API
import CORALean.Global.Float.Instances.Binary64.Operations.API
import CORALean.Global.Float.Instances.Binary64.Theorems.API
import CORALean.Global.Float.Instances.Binary64.Instances

/-!
# Native binary64, collected

What a `Float` denotes in `Binary64`, the directed operations in `Operations`,
what trusting the hardware would mean and the single axiom that trusts it in
`Definitions`, what follows from it in `Theorems`, and the `FloatOps` and
`SoundFloatArithmetic` instances in `Instances`.

`Definitions/Axioms.lean` holds the only assumption in the library, and the
only reason to reach for this backend rather than `Dyadic` is speed.
-/
