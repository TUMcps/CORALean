import CORALean.Arithmetic.Float.ContSet.Interval.Proofs.API

/-!
# What the floating-point `Interval` guarantees

Stated exactly as `Arithmetic.Real` states it — the same `⊆`, over the same sets
of real points — and proved the same way each time: the exact guarantee composed
with the refinement. `Proofs` therefore holds no set-level reasoning at all.
-/

namespace CORALean.Arithmetic.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m h : ℕ}

theorem Interval.plus_outer (I₁ I₂ : Interval 𝕋 n) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct :=
  subset_trans (Real.Interval.plus_outer I₁.nominal I₂.nominal) (Interval.Proofs.plus_outer_refines I₁ I₂)

theorem Interval.mtimes_outer (M : Mat 𝕋 m n) (I : Interval 𝕋 n) :
    ((toRealMat M) *ᵥ ·) '' I.construct ⊆ (Interval.mtimes M I).construct :=
  subset_trans (Real.Interval.mtimes_outer (toRealMat M) I.nominal)
    (Interval.Proofs.mtimes_outer_refines M I)

theorem Interval.sub_mem_residual {lo hi stored : Vec 𝕋 n} {x : Vec ℝ n}
    (h : ∀ i, toReal (lo i) ≤ x i ∧ x i ≤ toReal (hi i)) :
    (fun i => x i - toReal (stored i)) ∈ (Interval.residual lo hi stored).construct :=
  Interval.Proofs.sub_mem_residual h

end CORALean.Arithmetic.Float
