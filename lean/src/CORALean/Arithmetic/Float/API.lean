import CORALean.Arithmetic.Float.SoundFloatArithmetic
import CORALean.Arithmetic.Float.Instances
import CORALean.Arithmetic.Float.ContSet.Interval.Instance
import CORALean.Arithmetic.Float.ContSet.Zonotope.Instance
import CORALean.Arithmetic.Float.ContSet.InflatedContSet.Theorems

/-!
# Floating-point arithmetic, collected

The refinement layer: the same representations, computed with rounded
arithmetic. Soundness is stated in the same `⊆` as `Arithmetic.Real`, because a
float zonotope denotes a set of real points just as an exact one does.

The scalar model and its instances, then the representations built over it.
-/
