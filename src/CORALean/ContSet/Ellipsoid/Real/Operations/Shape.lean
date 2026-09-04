import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# `Ellipsoid.shape`

CORA's shape matrix `Q = G Gᵀ`, recovered from the generator matrix this
representation stores instead, so the correspondence to CORA can be checked
rather than taken on trust.

Nothing else in the development uses it: every operation and every guarantee is
stated against `G`, which is what avoids a positive-semi-definiteness side
condition and a matrix square root.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

def Ellipsoid.shape (E : Ellipsoid n) : Mat ℝ n n := E.G * E.Gᵀ

end CORALean.Real
