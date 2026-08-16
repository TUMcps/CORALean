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

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {F : Type} [FloatOps F] [SoundFloatArithmetic F] {n m h : ℕ}

theorem Interval.plus_sound (I₁ I₂ : Interval F n) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct :=
  subset_trans (Real.Interval.plus_sound I₁.nominal I₂.nominal) (Interval.Proofs.plus_refines I₁ I₂)

theorem Interval.mtimes_sound (M : Mat F m n) (I : Interval F n) :
    ((toRealMat M) *ᵥ ·) '' I.construct ⊆ (Interval.mtimes M I).construct :=
  subset_trans (Real.Interval.mtimes_sound (toRealMat M) I.nominal)
    (Interval.Proofs.mtimes_refines M I)

theorem Interval.sub_mem_residual {lo hi stored : Vec F n} {x : Vec ℝ n}
    (h : ∀ i, toReal (lo i) ≤ x i ∧ x i ≤ toReal (hi i)) :
    (fun i => x i - toReal (stored i)) ∈ (Interval.residual lo hi stored).construct :=
  Interval.Proofs.sub_mem_residual h

theorem Interval.mem_generatorError {d : Mat F n h} {Δ : Mat ℝ n h} {β : Vec ℝ h}
    (hd : ∀ i j, |Δ i j| ≤ toReal (d i j)) (hβ : ∀ j, |β j| ≤ 1) :
    (fun i => ∑ j, Δ i j * β j) ∈ (Interval.generatorError d).construct :=
  Interval.Proofs.mem_generatorError hd hβ

end CORALean.Arithmetic.Float
