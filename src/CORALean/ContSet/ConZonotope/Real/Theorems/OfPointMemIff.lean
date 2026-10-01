import CORALean.ContSet.ConZonotope.Real.Operations.OfPoint
import CORALean.ContSet.ConZonotope.Real.Theorems.OfPointMem

/-!
# `ConZonotope.ofPoint` denotes exactly one point

The converse to `mem_ofPoint`: no generator leaves no coefficient to spend.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mem_ofPoint_iff (v x : α) :
    x ∈ (ConZonotope.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · rintro ⟨β, _, _, h⟩
    simpa [ConZonotope.ofPoint] using h
  · rintro rfl
    exact ConZonotope.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
