module

public import CORALean.Global.Float.FloatOps
public import CORALean.Global.Float.GenOpNorm
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Float.DecidableToReal
public import CORALean.Global.Float.ExactLe
public import CORALean.Global.Float.TimeOrder
public import CORALean.Global.Float.NoNaN
public import CORALean.Global.Float.EuclideanNorm
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Log
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Float.InverseHyperbolic
public import CORALean.Global.Float.SinCos
public import CORALean.Global.Float.TrigRange
public import CORALean.Global.Float.InverseTrig
public import CORALean.Global.Float.Tan
public import CORALean.Global.Float.Hyperbolic
public import CORALean.Global.Float.Atanh
public import CORALean.Global.Float.GenBlockDiag
public import CORALean.Global.Float.ToRealMatMulVec
public import CORALean.Global.Float.MulDownGap
public import CORALean.Global.Float.ListSum
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.DivFact
public import CORALean.Global.Float.BilinUp
public import CORALean.Global.Float.Instances.API
public import CORALean.Global.Float.FloatBound
public import CORALean.Global.Float.RatUp
public import CORALean.Global.Float.IntRound
public import CORALean.Global.Float.HalfPow
public import CORALean.Global.Float.InvSqrtOneSub

/-!
# The floating-point scalar, collected

`FloatOps` gives the rounded operations, `SoundFloatArithmetic` says their
directions are honest, `ToRat` decodes a scalar exactly into ℚ where one can,
`ExactLe` compares two scalars as reals through it, `DecidableToReal` decides those comparisons,
`TimeOrder` orders time stamps by them, `Exp` and `Log` are the transcendentals built on top of
them, `SinCos` the sine and cosine by halving and doubling, `InverseTrig` the
arctangent, arcsine and arccosine by a bisection on them, and `Instances`
supplies models of both classes.

`EuclideanNorm` is the third place the scalar is asked for something it has not
got, and the three answers differ: `exp` is a construction, because no
expression in `+`, `*`, `min`, `max` and halving dominates it; a square root is
dominated by one, so `‖·‖₂` needs only a *check* — a candidate `s` and
`x ≤ s·s`; and `log` inverts a construction, so a bisection whose every step is
a check turns `Exp` into a value, adding no operation either. `FloatBound` is `SupportFunction`'s
`SupportBound` stored in the scalar, its composition rules rounded upward.

Not reachable through `Global.API`: a float representation imports this
directly, so that the specification layer never depends on it.
-/
