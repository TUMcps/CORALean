import CORALean.Arithmetic.Real.ContSet.Interval.Proofs

/-!
# What `Interval` guarantees

One entry per operation in `API`, stated in full and discharged by the lemma of
the same name in `Interval.Proofs`.

Nothing claims exactness even where the operation is exact: callers may rely
only on over-approximation.
-/

namespace CORALean.Arithmetic.Real

open Matrix Pointwise

variable {n m : ℕ}

theorem Interval.plus_sound (I₁ I₂ : Interval n) :
    I₁.construct + I₂.construct ⊆ (I₁.plus I₂).construct :=
  Interval.Proofs.plus_sound I₁ I₂

theorem Interval.mtimes_sound (M : Mat ℝ m n) (I : Interval n) :
    (M *ᵥ ·) '' I.construct ⊆ (Interval.mtimes M I).construct :=
  Interval.Proofs.mtimes_sound M I

end CORALean.Arithmetic.Real
