import CORALean.Global.Float.FloatOps
import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.Global.Float.EuclideanNorm
import CORALean.Global.Float.Exp
import CORALean.Global.Float.Log
import CORALean.Global.Float.Instances.API
import CORALean.Global.Float.FloatBound

/-!
# The floating-point scalar, collected

`FloatOps` gives the rounded operations, `SoundFloatArithmetic` says their
directions are honest, `Exp` and `Log` are the transcendentals built on top of
them, and `Instances` supplies models of both classes.

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
