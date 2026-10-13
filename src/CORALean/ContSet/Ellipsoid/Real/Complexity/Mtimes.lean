import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes

/-!
# `Ellipsoid.mtimes_k`

`mtimes` sends `G` to `M G`, an `m × k` matrix from an `n × k` one, so the
generator count carries over exactly. `rfl`, since `Operations/Mtimes.lean`
states `k` directly.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mtimes_k (M : Mat ℝ m n) (E : Ellipsoid n) :
    (Ellipsoid.mtimes M E).k = E.k := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
