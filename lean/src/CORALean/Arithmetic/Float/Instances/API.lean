import CORALean.Arithmetic.Float.Instances.Real.API
import CORALean.Arithmetic.Float.Instances.Dyadic.API

/-!
# Models of `SoundFloatArithmetic`

ℝ, where rounding is trivial, and `Dyadic p`, where it is not. Two instances
rather than one is the point: an axiom that only a rounding arithmetic can
violate is invisible against ℝ alone.
-/
