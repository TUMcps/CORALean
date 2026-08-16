import CORALean.Arithmetic.Float.ContSet.Interval.Proofs

/-!
# What the floating-point `Interval` guarantees

Stated exactly as `Arithmetic.Real` states it — the same `⊆`, over the same sets
of real points — and proved the same way each time: the exact guarantee, then
the refinement, composed.

`Proofs` therefore contains no set-level reasoning at all. That is the point of
stating soundness as `⊆` once.
-/

namespace CORALean.Arithmetic.Float

open Pointwise Matrix

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n m : ℕ}

theorem Interval.plus_sound (I₁ I₂ : Interval F n) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct :=
  subset_trans (Real.Interval.plus_sound I₁.nominal I₂.nominal) (Interval.Proofs.plus_refines I₁ I₂)

theorem Interval.mtimes_sound (M : Mat F m n) (I : Interval F n) :
    ((toRealMat M) *ᵥ ·) '' I.construct ⊆ (Interval.mtimes M I).construct :=
  subset_trans (Real.Interval.mtimes_sound (toRealMat M) I.nominal)
    (Interval.Proofs.mtimes_refines M I)

end CORALean.Arithmetic.Float
