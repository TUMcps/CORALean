import CORALean.ContSet.Ellipsoid.Real.Operations.OfPoint
import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstruct

/-!
# A generator-free ellipsoid contains its own centre

`ofPoint v` reuses `mem_construct` at `u = 0 : Vec ℝ 0`, the only coefficient
vector a `0`-column `G` admits, in `unitBall₂` because `norm₂_zero ≤ 1`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mem_ofPoint (v : Vec ℝ n) : v ∈ (Ellipsoid.ofPoint v).construct := by
  have hu : ‖(0 : Vec ℝ 0)‖₂ ≤ 1 := mem_unitBall₂.mp zero_mem_unitBall₂
  simpa [Ellipsoid.ofPoint] using Ellipsoid.mem_construct (E := Ellipsoid.ofPoint v) hu

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
