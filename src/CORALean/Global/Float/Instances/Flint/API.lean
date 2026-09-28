import CORALean.Global.Float.Instances.Flint.Flint
import CORALean.Global.Float.Instances.Flint.Definitions.API
import CORALean.Global.Float.Instances.Flint.Operations.API
import CORALean.Global.Float.Instances.Flint.Theorems.API
import CORALean.Global.Float.Instances.Flint.Instances

/-!
# FLINT-rounded dyadics, collected

The representation in `Flint`, the operations in `Operations` (six of them
calls into FLINT), what trusting FLINT means and the one axiom that trusts it
in `Definitions`, the exact operations' guarantees in `Theorems`, and the
`FloatOps` and `SoundFloatArithmetic` instances in `Instances`.

Optional. Nothing in the default targets imports this, because running it needs
the C library: only the `bench-flint` executable links FLINT (README, "FLINT
backend (optional)"), and `scripts/check-axioms.sh` imports it to check that
`trustedFlint` stays inside it.
-/
