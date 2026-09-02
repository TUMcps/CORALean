import CORALean.Global.Float.FloatOps
import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.Global.Float.Exp
import CORALean.Global.Float.Instances.API
import CORALean.Global.LinProg.Float.API

/-!
# The floating-point scalar, collected

`FloatOps` gives the rounded operations, `SoundFloatArithmetic` says their
directions are honest, `Exp` is the one transcendental built on top of them, and
`Instances` supplies models of both classes.

Not reachable through `Global.API`: a float representation imports this
directly, so that the specification layer never depends on it.
-/
