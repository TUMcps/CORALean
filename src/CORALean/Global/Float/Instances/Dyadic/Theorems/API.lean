import CORALean.Global.Float.Instances.Dyadic.Theorems.Exact
import CORALean.Global.Float.Instances.Dyadic.Theorems.Rounding
import CORALean.Global.Float.Instances.Dyadic.Theorems.Order
import CORALean.Global.Float.Instances.Dyadic.Theorems.Division

/-!
# What `Dyadic` guarantees

The obligations `SoundFloatArithmetic` states, split by which step incurs them:
`Exact` for the operations that lose nothing, `Rounding` for the two that do,
`Order` for the comparison, `Division` for the one operation with no exact step
to compose with. `Instance` assembles them.
-/
