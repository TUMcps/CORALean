import CORALean.Arithmetic.Float.SoundFloatArithmetic

/-!
# Floating-point arithmetic, collected

The refinement layer: the same representations, computed with rounded
arithmetic. Soundness is stated in the same `⊆` as `Arithmetic.Real`, because a
float zonotope denotes a set of real points just as an exact one does.

Currently the scalar model only; the representations follow.
-/
