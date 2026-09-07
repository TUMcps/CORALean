import CORALean.ContSet.Capsule.Real.Capsule

/-!
# `Capsule.ofPoint`

CORA's `capsule` at a centre, no direction and no radius: a single point, as
the representation. What `OfPoint` asks every representation with a point
operation to supply.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A single point, as a capsule with no direction and no radius. -/
def Capsule.ofPoint (v : Vec ℝ n) : Capsule n := ⟨v, 0, 0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
