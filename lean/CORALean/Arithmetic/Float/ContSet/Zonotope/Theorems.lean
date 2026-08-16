import CORALean.Arithmetic.Float.ContSet.Zonotope.Proofs

/-!
# What the floating-point `Zonotope` guarantees

Stated exactly as `Arithmetic.Real` states it, over the same sets of real
points. Only the generator count differs from nothing at all: `plus` returns `h + k`, as
over ℝ, because the rounding went into the box instead. `absorbError` is the one
operation that spends generators, `h + n`, and it is the caller's choice.
-/

namespace CORALean.Arithmetic.Float

open Pointwise Matrix SoundFloatArithmetic

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n m h k q r : ℕ}

theorem Zonotope.plus_sound (Z₁ : Zonotope F n h) (Z₂ : Zonotope F n k) :
    Z₁.construct + Z₂.construct ⊆ (Z₁.plus Z₂).construct :=
  Zonotope.Proofs.plus_sound Z₁ Z₂

theorem Zonotope.mtimes_sound (M : Mat F m n) (Z : Zonotope F n h) :
    ((toRealMat M) *ᵥ ·) '' Z.construct ⊆ (Zonotope.mtimes M Z).construct :=
  Zonotope.Proofs.mtimes_sound M Z

theorem Zonotope.reduce_sound (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduce part).construct :=
  Zonotope.Proofs.reduce_sound Z part

theorem Zonotope.reduceAndAbsorb_sound (Z : Zonotope F n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduceAndAbsorb part).construct :=
  Zonotope.Proofs.reduceAndAbsorb_sound Z part

theorem Zonotope.absorbError_sound (Z : Zonotope F n h) :
    Z.construct ⊆ Z.absorbError.construct :=
  Zonotope.Proofs.absorbError_sound Z

end CORALean.Arithmetic.Float
