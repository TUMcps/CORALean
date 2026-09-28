import CORALean.Global.Float.Instances.IEEE.Theorems.AddDownLeAdd
import CORALean.Global.Float.Instances.IEEE.Theorems.AddLeAddUp
import CORALean.Global.Float.Instances.IEEE.Theorems.DivDownLeDiv
import CORALean.Global.Float.Instances.IEEE.Theorems.DivLeDivUp
import CORALean.Global.Float.Instances.IEEE.Theorems.LeIff
import CORALean.Global.Float.Instances.IEEE.Theorems.LeRoundUp
import CORALean.Global.Float.Instances.IEEE.Theorems.MulDownLeMul
import CORALean.Global.Float.Instances.IEEE.Theorems.MulLeMulUp
import CORALean.Global.Float.Instances.IEEE.Theorems.OverflowsIff
import CORALean.Global.Float.Instances.IEEE.Theorems.QminLeRoundDownExponent
import CORALean.Global.Float.Instances.IEEE.Theorems.QminLeRoundUpExponent
import CORALean.Global.Float.Instances.IEEE.Theorems.RoundDownLe
import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealHalf
import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealMaximum
import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealMinimum
import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealNeg

/-!
# What `IEEE` guarantees

The obligations `SoundFloatArithmetic` states: `LeRoundUp`/`RoundDownLe` for the two roundings,
composed with `Dyadic`'s exact steps into the six directed laws; `ToRealNeg`/`ToRealHalf`/`LeIff`
and what reads off it for the exact operations. Beside them what makes the grid the format's:
`QminLeRoundUpExponent`/`QminLeRoundDownExponent`, no result finer than the smallest subnormal,
and `OverflowsIff`, what the overflow check detects. `Instances` assembles the class.
-/
