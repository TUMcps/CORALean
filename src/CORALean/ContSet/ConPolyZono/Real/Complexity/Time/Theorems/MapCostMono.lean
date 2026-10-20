module

public import CORALean.Global.Cost
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Map

@[expose] public section

/-!
# `ConPolyZono.mapCost_mono`

Monotone in the factor count, both generator counts and the constraint sizes, so bounds on the
operand's sizes give a bound on the cost.

## Inputs
* `p` – smaller factor count
* `p'` – larger factor count
* `h` – smaller dependent generators
* `h'` – larger dependent generators
* `qI` – smaller independent generators
* `q'` – larger independent generators
* `m` – smaller constraint count
* `m'` – larger constraint count
* `q` – smaller constraint generators
* `q''` – larger constraint generators
* `cf` – cost of one application

## Hypotheses
* `hp` – factor counts are ordered
* `hh` – dependent generator counts are ordered
* `hq` – independent generator counts are ordered
* `hm` – constraint counts are ordered
* `hc` – constraint generator counts are ordered

## Conclusion
* the cost is monotone in all the counts
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
theorem ConPolyZono.mapCost_mono {p p' h h' qI q' m m' q q'' : ℕ} (cf : Cost) (hp : p ≤ p')
    (hh : h ≤ h') (hq : qI ≤ q') (hm : m ≤ m') (hc : q ≤ q'') :
    ConPolyZono.mapCost cf p h qI m q ≤ ConPolyZono.mapCost cf p' h' q' m' q'' := by
  cost_mono [ConPolyZono.mapCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
