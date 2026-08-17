import CORALean.Arithmetic.Real.ContSet.Zonotope.Proofs

/-!
# What `Zonotope` guarantees

One entry per operation in `API`, stated in full and discharged by the lemma of
the same name in `Zonotope.Proofs`. Restating the type is the price for keeping
proofs elsewhere; it is checked against the proved one, so the two cannot drift.
-/

namespace CORALean.Arithmetic.Real

open Matrix Pointwise

variable {n m h k q r : ℕ}

theorem Zonotope.plus_exact (Z₁ : Zonotope n h) (Z₂ : Zonotope n k) :
    Z₁.construct + Z₂.construct = (Z₁.plus Z₂).construct :=
  Zonotope.Proofs.plus_exact Z₁ Z₂

theorem Zonotope.mtimes_exact (M : Mat ℝ m n) (Z : Zonotope n h) :
    (M *ᵥ ·) '' Z.construct = (Zonotope.mtimes M Z).construct :=
  Zonotope.Proofs.mtimes_exact M Z

theorem Zonotope.interval_outer (Z : Zonotope n h) :
    Z.construct ⊆ Z.interval.construct :=
  Zonotope.Proofs.interval_outer Z

theorem Zonotope.reduce_outer (Z : Zonotope n h)
    (part : Split (Fin h) into (Fin q) and (Fin r)) :
    Z.construct ⊆ (Z.reduce part).construct :=
  Zonotope.Proofs.reduce_outer Z part

end CORALean.Arithmetic.Real
