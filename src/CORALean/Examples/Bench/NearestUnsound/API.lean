import CORALean.Examples.Bench.NearestUnsound.Axioms
import CORALean.Examples.Bench.NearestUnsound.Instances
import CORALean.Examples.Bench.NearestUnsound.NearestDyadic
import CORALean.Examples.Bench.NearestUnsound.NearestFloat
import CORALean.Examples.Bench.NearestUnsound.NearestUnsound
import CORALean.Examples.Bench.NearestUnsound.Tainted

/-!
# Round-to-nearest scalars, collected: NO GUARANTEES

The paper's "round-to-nearest (as in CORA)" baseline and nothing else.
`NearestFloat` is native binary64 and `NearestDyadic p` a `p`-bit format, both
rounding to nearest where `SoundFloatArithmetic` asks for a direction. Their
rounding laws are the fields of `NearestUnsound`, FALSE by design, assumed once
as `nearestUnsound` in `Axioms`; every other law is proved in `Instances`.

No library theorem depends on that axiom: only `Examples/Bench/` may import this
directory, which `scripts/check-conventions.sh` enforces, and
`scripts/check-axioms.sh` asks Lean whether any declaration outside the bench
reaches it. `Tainted` is its positive control. The instances are `scoped` to
`CORALean.Bench.NearestUnsound`, opened only where `--type nearest` dispatches.
-/
