module

public import CORALean.Global.Cost
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Theorems.MapCostMono

@[expose] public section

/-!
# `ConZonotope.mtimesCost_mono`

Monotone in the generator count and the row counts, so a bound on the operand's size gives a
bound on the cost.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count and the row counts, so a bound on the operand's size gives a
bound on the cost. -/
theorem ConZonotope.mtimesCost_mono {h h' r r' re re' : ℕ} (m n : ℕ) (hh : h ≤ h') (hr : r ≤ r')
    (he : re ≤ re') :
    ConZonotope.mtimesCost m n h r re ≤ ConZonotope.mtimesCost m n h' r' re' :=
  ConZonotope.mapCost_mono _ hh hr he

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
