module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# An ellipsoid is an affine image of the unit ball

The definition already is one; this spells it as `Set.image` so that convexity
and compactness transfer from `unitBall₂` in a single step instead of being
re-proved over the existential.

Both directions are the same destructuring, the image and the set-builder
agreeing definitionally.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.construct_eq_image (E : Ellipsoid n) :
    E.construct = (fun u : Vec ℝ n => E.q + E.G *ᵥ u) '' unitBall₂ n := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
