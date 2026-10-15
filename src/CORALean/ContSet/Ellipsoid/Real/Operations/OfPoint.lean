module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.ofPoint`

CORA's `ellipsoid(zeros(n), v)`: the zero shape matrix, a degenerate ellipsoid denoting the single
point `v`. What `OfPoint` asks every representation with a point operation to supply.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A single point, as an ellipsoid with the zero shape matrix. -/
def Ellipsoid.ofPoint (v : Vec ℝ n) : Ellipsoid n := ⟨0, v, .zero⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
