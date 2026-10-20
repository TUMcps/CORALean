module

public import CORALean.Global.Cost
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.ConZonotope.Real.Operations.Map

@[expose] public section

/-!
# `ConZonotope.mapCost_mono`

Monotone in the generator count and the row counts, so a bound on the operand's size gives a
bound on the cost.

## Inputs
* `h` – generators
* `h'` – larger generator count
* `r` – inequalities
* `r'` – larger inequality count
* `re` – equalities
* `re'` – larger equality count
* `cf` – cost of the map on one vector

## Hypotheses
* `hh` – `h ≤ h'`
* `hr` – `r ≤ r'`
* `he` – `re ≤ re'`

## Conclusion
* the cost of mapping is monotone in the sizes
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
theorem ConZonotope.mapCost_mono {h h' r r' re re' : ℕ} (cf : Cost) (hh : h ≤ h') (hr : r ≤ r')
    (he : re ≤ re') :
    ConZonotope.mapCost cf h r re ≤ ConZonotope.mapCost cf h' r' re' := by
  cost_mono [ConZonotope.mapCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
