import CORALean.Arithmetic.Real.ContSet.Zonotope.Proofs.API

/-!
# What `Zonotope` guarantees

One entry per operation, stated in full and discharged by the lemma of
the same name in `Zonotope.Proofs`. Restating the type is the price for keeping
proofs elsewhere; it is checked against the proved one, so the two cannot drift.
-/

namespace CORALean.Arithmetic.Real

open Matrix Pointwise

variable {n m : ℕ}

theorem Zonotope.plus_exact (Z₁ Z₂ : Zonotope n) :
    Z₁.construct + Z₂.construct = (Z₁.plus Z₂).construct :=
  Zonotope.Proofs.plus_exact Z₁ Z₂

theorem Zonotope.mtimes_exact (M : Mat ℝ m n) (Z : Zonotope n) :
    (M *ᵥ ·) '' Z.construct = (Zonotope.mtimes M Z).construct :=
  Zonotope.Proofs.mtimes_exact M Z

theorem Zonotope.interval_outer (Z : Zonotope n) :
    Z.construct ⊆ Z.interval.construct :=
  Zonotope.Proofs.interval_outer Z

/-! ### reduce -/

theorem Zonotope.reduceGirard_outer (Z : Zonotope n) (o : ℕ) :
    Z.construct ⊆ (Z.reduceGirard o).construct :=
  Zonotope.Proofs.reduceGirard_outer Z o

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem Zonotope.reduce_outer (Z : Zonotope n) (o : ℕ) :
    Z.construct ⊆ (Z.reduce o).construct :=
  Zonotope.reduceGirard_outer Z o

end CORALean.Arithmetic.Real
