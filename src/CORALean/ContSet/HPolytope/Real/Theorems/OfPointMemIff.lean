import CORALean.ContSet.HPolytope.Real.Operations.OfPoint
import CORALean.ContSet.HPolytope.Real.Theorems.OfPointMem

/-!
# `HPolytope.ofPoint` denotes exactly one point

The converse to `mem_ofPoint`: the `n` equality rows pin every coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_ofPoint_iff (v x : Vec ℝ n) :
    x ∈ (HPolytope.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · rintro ⟨-, h⟩
    funext i
    exact h i
  · rintro rfl
    exact HPolytope.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
