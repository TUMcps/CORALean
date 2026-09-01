import CORALean.Global.Float.FloatOps
import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.Global.Float.Instances.API

/-!
# The floating-point scalar, collected

`FloatOps` gives the rounded operations, `SoundFloatArithmetic` says their
directions are honest, and `Instances` supplies models of both.

`Global.API` does not import this. Every `Real` file imports `Global.API`, so
pulling the float scalar in there would make deleting `Float` break the
specification layer. A float representation imports this directly instead.
-/
