module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.ofPoint`

CORA's `ellipsoid` at a centre and no generators: a degenerate ellipsoid, its
`G` the `n × 0` matrix, denoting the single point `v`. What `OfPoint` asks
every representation with a point operation to supply.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A single point, as an ellipsoid with no generators. -/
def Ellipsoid.ofPoint (v : Vec ℝ n) : Ellipsoid n := ⟨0, v, 0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
