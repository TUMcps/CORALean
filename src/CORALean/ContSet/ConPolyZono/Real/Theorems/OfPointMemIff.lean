import CORALean.ContSet.ConPolyZono.Real.Operations.OfPoint
import CORALean.ContSet.ConPolyZono.Real.Theorems.OfPointMem
import Mathlib.Algebra.Group.Fin.Tuple

/-!
# `ConPolyZono.ofPoint` denotes exactly one point

The converse to `mem_ofPoint`: no generator of either kind leaves nothing to add to
the centre.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mem_ofPoint_iff (v x : α) :
    x ∈ (ConPolyZono.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · rintro ⟨a, β, _, _, _, h⟩
    simpa [ConPolyZono.ofPoint] using h
  · rintro rfl
    exact ConPolyZono.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
