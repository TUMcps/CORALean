module

public import CORALean.Global.Float.Instances.IEEE.Theorems.Basic
public import CORALean.Global.Float.Instances.IEEE.Theorems.LeRoundUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.OverflowsIff
public import CORALean.Global.Float.Instances.IEEE.Theorems.QminLeRoundDownExponent
public import CORALean.Global.Float.Instances.IEEE.Theorems.QminLeRoundUpExponent
public import CORALean.Global.Float.Instances.IEEE.Theorems.RoundDownLe
public import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealMaximum
public import CORALean.Global.Float.Instances.IEEE.Theorems.ToRealMinimum

/-!
# What `IEEE` guarantees

The obligations `SoundFloatArithmetic` states: `LeRoundUp`/`RoundDownLe` for the two roundings,
composed with `Dyadic`'s exact steps into the six directed laws; `ToRealNeg`/`ToRealHalf`/`LeIff`
and what reads off it for the exact operations. Beside them what makes the grid the format's:
`QminLeRoundUpExponent`/`QminLeRoundDownExponent`, no result finer than the smallest subnormal,
and `OverflowsIff`, what the overflow check detects. `Instances` assembles the class.
-/
