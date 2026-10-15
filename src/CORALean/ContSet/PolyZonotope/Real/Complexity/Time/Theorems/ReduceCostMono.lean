module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.CompactCostMono
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.ReduceGirardCostMono
public import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceCost

@[expose] public section

/-!
# `PolyZonotope.reduceCost_mono`

Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.reduceCost_mono {h h' q q' : ℕ} (n p : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.reduceCost n p h q ≤ PolyZonotope.reduceCost n p h' q' :=
  Cost.add_le_add (PolyZonotope.compactCost_mono n p hh)
    (PolyZonotope.reduceGirardCost_mono n hh hq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
