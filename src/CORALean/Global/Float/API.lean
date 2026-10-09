import CORALean.Global.Float.FloatOps
import CORALean.Global.Float.GenOpNorm
import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.Global.Float.ToRat
import CORALean.Global.Float.NoNaN
import CORALean.Global.Float.EuclideanNorm
import CORALean.Global.Float.Exp
import CORALean.Global.Float.Log
import CORALean.Global.Float.Sqrt
import CORALean.Global.Float.InverseHyperbolic
import CORALean.Global.Float.SinCos
import CORALean.Global.Float.TrigRange
import CORALean.Global.Float.InverseTrig
import CORALean.Global.Float.Tan
import CORALean.Global.Float.Hyperbolic
import CORALean.Global.Float.Atanh
import CORALean.Global.Float.GenBlockDiag
import CORALean.Global.Float.ListSum
import CORALean.Global.Float.PowUp
import CORALean.Global.Float.PowDown
import CORALean.Global.Float.DivFact
import CORALean.Global.Float.BilinUp
import CORALean.Global.Float.Instances.API
import CORALean.Global.Float.FloatBound
import CORALean.Global.Float.RatUp
import CORALean.Global.Float.IntRound
import CORALean.Global.Float.HalfPow
import CORALean.Global.Float.InvSqrtOneSub

/-!
# The floating-point scalar, collected

`FloatOps` gives the rounded operations, `SoundFloatArithmetic` says their
directions are honest, `ToRat` decodes a scalar exactly into ℚ where one can,
`Exp` and `Log` are the transcendentals built on top of
them, `SinCos` the sine and cosine by halving and doubling, `InverseTrig` the
arctangent, arcsine and arccosine by a bisection on them, and `Instances`
supplies models of both classes.

`EuclideanNorm` is the third place the scalar is asked for something it has not
got, and the three answers differ: `exp` is a construction, because no
expression in `+`, `*`, `min`, `max` and halving dominates it; a square root is
dominated by one, so `‖·‖₂` needs only a *check* — a candidate `s` and
`x ≤ s·s`; and `log` inverts a construction, so a bisection whose every step is
a check turns `Exp` into a value, adding no operation either. `FloatBound` is `LinProg`'s
`SupportBound` stored in the scalar, its composition rules rounded upward.

Not reachable through `Global.API`: a float representation imports this
directly, so that the specification layer never depends on it.
-/
