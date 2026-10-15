module

public import CORALean.Global.Cost
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.MtimesIntervalMatCost
public import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.MtimesIntervalMatCostMono

@[expose] public section

/-!
# `ConZonotope.mtimesIntervalMatCost_mono`

Monotone in the generator count and the row counts, so a bound on the operand's size gives a
bound on the cost.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count and the row counts, so a bound on the operand's size gives a
bound on the cost. -/
theorem ConZonotope.mtimesIntervalMatCost_mono {h h' r r' re re' : ℕ} (m n : ℕ) (hh : h ≤ h')
    (hr : r ≤ r') (he : re ≤ re') :
    ConZonotope.mtimesIntervalMatCost m n h r re ≤
      ConZonotope.mtimesIntervalMatCost m n h' r' re' := by -- --- PROOF ---
  have := Cost.le_iff.mp (Zonotope.mtimesIntervalMatCost_mono m n hh)
  simp only [ConZonotope.mtimesIntervalMatCost, Cost.le_iff, Cost.ops_add]
  have g : n * (1 + h) + (r + re) * (h + m + 1) ≤ n * (1 + h') + (r' + re') * (h' + m + 1) := by
    gcongr
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
