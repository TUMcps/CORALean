module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.ReduceGirardCostMono
public import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceCost

@[expose] public section

/-!
# `PolyZonotope.reduceCost_mono`

Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost.

## Inputs
* `h` – dependent generator count
* `h'` – larger dependent generator count
* `q` – independent generator count
* `q'` – larger independent generator count
* `n` – dimension
* `p` – number of factors

## Hypotheses
* `hh` – dependent count grows
* `hq` – independent count grows

## Conclusion
* the cost does not decrease
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Monotone in both generator counts, so a bound on the operand's size gives a
bound on the cost. -/
private theorem PolyZonotope.aux_compactCost_mono {h h' q q' : ℕ} (n p : ℕ) (hh : h ≤ h')
    (hq : q ≤ q') :
    PolyZonotope.step_compactCost n p h q ≤ PolyZonotope.step_compactCost n p h' q' := by
  cost_mono [PolyZonotope.step_compactCost]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.reduceCost_mono {h h' q q' : ℕ} (n p : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.reduceCost n p h q ≤ PolyZonotope.reduceCost n p h' q' :=
  Cost.add_le_add (PolyZonotope.aux_compactCost_mono n p hh hq)
    (PolyZonotope.reduceGirardCost_mono n p hh hq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
