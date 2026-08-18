import CORALean.Arithmetic.Float.FloatOps
import CORALean.Arithmetic.Float.SoundFloatArithmetic
import CORALean.Arithmetic.Float.Instances.API
import CORALean.Arithmetic.Float.ContSet.API

/-!
# Floating-point arithmetic, collected

The refinement layer: the same representations, computed with rounded
arithmetic. Soundness is stated in the same `⊆` as `Arithmetic.Real`, because a
float zonotope denotes a set of real points just as an exact one does.

The scalar model and its instances, then the representations built over it.

Only representations. An algorithm in `Real.ContDynamics` is generic over
`OuterContSet`, and a float representation instantiates that class like any
other, so it inherits the algorithm's guarantee with no float counterpart to
write. The rounding is paid once, in the operations.
-/
