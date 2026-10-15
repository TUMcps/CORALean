module

public import CORALean.Global.Cost
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Theorems.MapCostMono

@[expose] public section

/-!
# `ConPolyZono.mtimesCost_mono`

Monotone in the factor count, both generator counts and the constraint sizes, so bounds on the
operand's sizes give a bound on the cost.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the factor count, both generator counts and the constraint sizes, so bounds on the
operand's sizes give a bound on the cost. -/
theorem ConPolyZono.mtimesCost_mono {p p' h h' qI q' m m' q q'' : ℕ} (k n : ℕ) (hp : p ≤ p')
    (hh : h ≤ h') (hq : qI ≤ q') (hm : m ≤ m') (hc : q ≤ q'') :
    ConPolyZono.mtimesCost k n p h qI m q ≤ ConPolyZono.mtimesCost k n p' h' q' m' q'' :=
  ConPolyZono.mapCost_mono _ hp hh hq hm hc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
