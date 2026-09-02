import CORALean.Global.Float.FloatOps
import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.Global.Float.EuclideanNorm
import CORALean.Global.Float.Exp
import CORALean.Global.Float.Instances.API
import CORALean.Global.LinProg.Float.API

/-!
# The floating-point scalar, collected

`FloatOps` gives the rounded operations, `SoundFloatArithmetic` says their
directions are honest, `Exp` is the one transcendental built on top of them, and
`Instances` supplies models of both classes.

`EuclideanNorm` is the other place the scalar is asked for something it has not
got, and the two answers differ: `exp` is a construction, because no expression
in `+`, `*`, `min`, `max` and halving dominates it; a square root is dominated by
one, so `‖·‖₂` needs only a *check* — a candidate `s` and `x ≤ s·s` — and adds
no operation at all.

Not reachable through `Global.API`: a float representation imports this
directly, so that the specification layer never depends on it.
-/
