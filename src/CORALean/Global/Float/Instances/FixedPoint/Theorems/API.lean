import CORALean.Global.Float.Instances.FixedPoint.Theorems.DivDownLeDiv
import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeDivUp
import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeIff
import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeRoundUp
import CORALean.Global.Float.Instances.FixedPoint.Theorems.MantissaPos
import CORALean.Global.Float.Instances.FixedPoint.Theorems.RoundDownLe
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealAlign
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealExactAdd
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealExactMul
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealHalf
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealLeOfLe
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMaximum
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMinimum
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMk
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMkZero
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealNeg

/-!
# What `FixedPoint` guarantees

The obligations `SoundFloatArithmetic` states, split by which step incurs
them: the `ToRealExact*`/`ToRealNeg`/`ToRealHalf`/`ToRealMkZero` family for the
operations that lose nothing, `RoundDownLe`/`LeRoundUp` for the two that round,
`LeIff` and what reads off it for the comparison, `DivDownLeDiv`/`LeDivUp` for
the one operation with no exact step to compose with. `Instances` assembles
them.
-/
