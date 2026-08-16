import CORALean.Arithmetic.Float.SoundFloatArithmetic
import CORALean.Arithmetic.Float.Instances
import CORALean.Arithmetic.Float.ContSet.Interval.Theorems

/-!
# Floating-point arithmetic, collected

The refinement layer: the same representations, computed with rounded
arithmetic. Soundness is stated in the same `⊆` as `Arithmetic.Real`, because a
float zonotope denotes a set of real points just as an exact one does.

Currently the scalar model and its instances; the representations follow.
-/
