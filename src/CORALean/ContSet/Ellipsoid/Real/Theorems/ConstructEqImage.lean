import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# An ellipsoid is an affine image of the unit ball

The definition already is one; this spells it as `Set.image` so that convexity
and compactness transfer from `unitBall₂` in a single step instead of being
re-proved over the existential.

Both directions are the same destructuring, the image and the set-builder
agreeing definitionally.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

theorem Ellipsoid.construct_eq_image (E : Ellipsoid n) :
    E.construct = (fun u : Vec ℝ E.k => E.q + E.G *ᵥ u) '' unitBall₂ E.k := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

end CORALean.Real
