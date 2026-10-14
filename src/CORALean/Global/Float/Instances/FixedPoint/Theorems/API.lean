module

public import CORALean.Global.Float.Instances.FixedPoint.Theorems.DivDownLeDiv
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeDivUp
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeIff
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.LeRoundUp
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.MantissaPos
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.RoundDownLe
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealAlign
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealExactAdd
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealExactMul
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealHalf
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.Basic
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMaximum
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMinimum

/-!
# What `FixedPoint` guarantees

The obligations `SoundFloatArithmetic` states, split by which step incurs
them: the `ToRealExact*`/`ToRealNeg`/`ToRealHalf`/`ToRealMkZero` family for the
operations that lose nothing, `RoundDownLe`/`LeRoundUp` for the two that round,
`LeIff` and what reads off it for the comparison, `DivDownLeDiv`/`LeDivUp` for
the one operation with no exact step to compose with. `Instances` assembles
them.
-/
