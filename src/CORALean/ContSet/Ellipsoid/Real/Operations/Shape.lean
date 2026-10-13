module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.shape`

CORA's shape matrix `Q = G Gᵀ`, recovered from the generator matrix this
representation stores instead, so the correspondence to CORA can be checked
rather than taken on trust.

Nothing else in the development uses it: every operation and every guarantee is
stated against `G`, which is what avoids a positive-semi-definiteness side
condition and a matrix square root.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.shape (E : Ellipsoid n) : Mat ℝ n n := E.G * E.Gᵀ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
