import CORALean.Global.Float.FloatOps
import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.Global.Float.Instances.API

/-!
# The floating-point scalar, collected

`FloatOps` gives the rounded operations, `SoundFloatArithmetic` says their
directions are honest, and `Instances` supplies models of both.

Not reachable through `Global.API`: a float representation imports this
directly, so that the specification layer never depends on it.
-/
