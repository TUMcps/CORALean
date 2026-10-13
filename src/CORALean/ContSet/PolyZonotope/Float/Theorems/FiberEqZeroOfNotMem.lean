import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Float.Theorems.RepIdem

/-!
# A column that is not its class's representative gathers nothing
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {p h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.fiber_eq_zero_of_notMem (E : Fin p → Fin h → ℕ) (Gr : Fin h → ℝ)
    {j : Fin h} (hj : j ∉ PolyZonotope.repKeep E) :
    Real.PolyZonotope.fiberSum (Real.PolyZonotope.rep E) Gr j = 0 := by -- --- PROOF ---
  rw [Real.PolyZonotope.fiberSum]
  refine Finset.sum_eq_zero fun l hl => ?_
  exfalso
  have hrl : Real.PolyZonotope.rep E l = j := (Finset.mem_filter.mp hl).2
  refine hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
  rw [← hrl, PolyZonotope.rep_idem]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
