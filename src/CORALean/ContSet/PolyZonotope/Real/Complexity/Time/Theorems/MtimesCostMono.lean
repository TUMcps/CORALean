module

public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.MapCostMono

@[expose] public section

/-!
# `PolyZonotope.mtimesCost_mono`

Monotone in the factor count and both generator counts, so bounds on the operand's sizes give
a bound on the cost.

## Inputs
* `p` – number of factors
* `p'` – larger factor count
* `h` – dependent generator count
* `h'` – larger dependent generator count
* `q` – independent generator count
* `q'` – larger independent generator count
* `m` – output dimension
* `n` – input dimension

## Hypotheses
* `hp` – factor count grows
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the factor count and both generator counts, so bounds on the operand's sizes give
a bound on the cost. -/
theorem PolyZonotope.mtimesCost_mono {p p' h h' q q' : ℕ} (m n : ℕ) (hp : p ≤ p') (hh : h ≤ h')
    (hq : q ≤ q') :
    PolyZonotope.mtimesCost m n p h q ≤ PolyZonotope.mtimesCost m n p' h' q' :=
  PolyZonotope.mapCost_mono _ hp hh hq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
