module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.AddDownLeAdd
public import CORALean.Global.Float.Instances.Dyadic.Theorems.AddLeAddUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.Basic
public import CORALean.Global.Float.Instances.Dyadic.Theorems.CoarsenDownLe
public import CORALean.Global.Float.Instances.Dyadic.Theorems.DivDownLeDiv
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeAlignedIff
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeCoarsenUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeDivUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeRoundUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeShlIff
public import CORALean.Global.Float.Instances.Dyadic.Theorems.MantissaPos
public import CORALean.Global.Float.Instances.Dyadic.Theorems.RoundDownLe
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealAlign
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDivEq
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactMul
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMaximum
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMinimum
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealShift
public import CORALean.Global.Float.Instances.Dyadic.Theorems.TwoZpowAlign
public import CORALean.Global.Float.Instances.Dyadic.Theorems.TwoZpowCoarsen

/-!
# What `Dyadic` guarantees

The obligations `SoundFloatArithmetic` states, split by which step incurs
them: the `ToRealExact*`/`ToRealNeg`/`ToRealHalf`/`ToRealMkZero` family for
the operations that lose nothing, `RoundDownLe`/`LeRoundUp` for the two that
round, `LeIff` and what reads off it for the comparison, `DivDownLeDiv`/
`LeDivUp` for the one operation with no exact step to compose with.
`Instance` assembles them.
-/
