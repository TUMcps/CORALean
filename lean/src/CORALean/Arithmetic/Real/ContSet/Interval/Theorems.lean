import CORALean.Arithmetic.Real.ContSet.Interval.Proofs.API

/-!
# What `Interval` guarantees

One entry per operation in `API`, stated in full and discharged by the lemma of
the same name in `Interval.Proofs`.
-/

namespace CORALean.Arithmetic.Real

open Matrix Pointwise

variable {n m : ℕ}

theorem Interval.isNonempty_iff (I : Interval n) : I.IsNonempty ↔ I.construct.Nonempty :=
  Interval.Proofs.isNonempty_iff I

theorem Interval.not_isNonempty_iff (I : Interval n) : ¬I.IsNonempty ↔ I.construct = ∅ :=
  Interval.Proofs.not_isNonempty_iff I

theorem Interval.plus_exact (I₁ I₂ : Interval n) (h₁ : I₁.IsNonempty) (h₂ : I₂.IsNonempty) :
    I₁.construct + I₂.construct = (I₁.plus I₂).construct :=
  Interval.Proofs.plus_exact I₁ I₂ h₁ h₂

theorem Interval.plus_outer (I₁ I₂ : Interval n) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct :=
  Interval.Proofs.plus_outer I₁ I₂

theorem Interval.mtimes_outer (M : Mat ℝ m n) (I : Interval n) :
    (M *ᵥ ·) '' I.construct ⊆ (Interval.mtimes M I).construct :=
  Interval.Proofs.mtimes_outer M I

end CORALean.Arithmetic.Real
