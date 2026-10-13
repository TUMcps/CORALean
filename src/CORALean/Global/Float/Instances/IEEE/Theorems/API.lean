module

public import CORALean.Global.Float.Instances.IEEE.Theorems.AddDownLeAdd
public import CORALean.Global.Float.Instances.IEEE.Theorems.AddLeAddUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.DivDownLeDiv
public import CORALean.Global.Float.Instances.IEEE.Theorems.DivLeDivUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.LeIff
public import CORALean.Global.Float.Instances.IEEE.Theorems.LeRoundUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.MulDownLeMul
public import CORALean.Global.Float.Instances.IEEE.Theorems.MulLeMulUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.OverflowsIff
public import CORALean.Global.Float.Instances.IEEE.Theorems.QminLeRoundDownExponent
public import CORALean.Global.Float.Instances.IEEE.Theorems.QminLeRoundUpExponent
public import CORALean.Global.Float.Instances.IEEE.Theorems.RoundDownLe
public import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealHalf
public import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealMaximum
public import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealMinimum
public import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealNeg

/-!
# What `IEEE` guarantees

The obligations `SoundFloatArithmetic` states: `LeRoundUp`/`RoundDownLe` for the two roundings,
composed with `Dyadic`'s exact steps into the six directed laws; `ToRealNeg`/`ToRealHalf`/`LeIff`
and what reads off it for the exact operations. Beside them what makes the grid the format's:
`QminLeRoundUpExponent`/`QminLeRoundDownExponent`, no result finer than the smallest subnormal,
and `OverflowsIff`, what the overflow check detects. `Instances` assembles the class.
-/
