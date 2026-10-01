import CORALean.ContSet.Ellipsoid.Real.Operations.OfPoint
import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMem

/-!
# `Ellipsoid.ofPoint` denotes exactly one point

The converse to `mem_ofPoint`: no generator, so `q + G u` is `q` for every `u`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mem_ofPoint_iff (v x : Vec ℝ n) :
    x ∈ (Ellipsoid.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · rintro ⟨u, -, h⟩
    simpa [Ellipsoid.ofPoint] using h
  · rintro rfl
    exact Ellipsoid.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
