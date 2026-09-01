import CORALean.Float.Instances.Dyadic.Theorems.Exact
import CORALean.Float.Instances.Dyadic.Theorems.Rounding
import CORALean.Float.Instances.Dyadic.Theorems.Order

/-!
# What `Dyadic` guarantees

The obligations `SoundFloatArithmetic` states, split by which step incurs them:
`Exact` for the operations that lose nothing, `Rounding` for the two that do,
`Order` for the comparison. `Instance` assembles them.
-/
