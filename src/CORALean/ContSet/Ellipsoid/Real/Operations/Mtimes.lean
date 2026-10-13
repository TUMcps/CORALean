import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# `Ellipsoid.mtimes`

CORA's `@ellipsoid/mtimes`, and the operation the generator form is chosen for:
the shape matrix would go `Q ↦ M Q Mᵀ`, which is a new `Q` to take a square root
of, while the generator goes `G ↦ M G` and nothing else changes.

The dimension moves and the generator count does not, which is why `G` has to be
allowed to be rectangular: `M G` is `m × k` from an `n × k`, and a square
generator matrix could not have held it.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.mtimes (M : Mat ℝ m n) (E : Ellipsoid n) : Ellipsoid m where
  k := E.k
  q := M *ᵥ E.q
  G := M * E.G

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
