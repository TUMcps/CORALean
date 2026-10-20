module

public import CORALean.Global.Cost
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.ReduceCost
public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.ReduceGirardCostMono

@[expose] public section

/-!
# `ConZonotope.reduceCost_mono`

Monotone in the generator count and the row counts, so a bound on the operand's size gives a
bound on the cost.

## Inputs
* `h` – generators
* `h'` – larger generator count
* `r` – inequalities
* `r'` – larger inequality count
* `re` – equalities
* `re'` – larger equality count
* `n` – dimension

## Hypotheses
* `hh` – `h ≤ h'`
* `hr` – `r ≤ r'`
* `he` – `re ≤ re'`

## Conclusion
* the cost of order reduction is monotone in the sizes
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
theorem ConZonotope.reduceCost_mono {h h' r r' re re' : ℕ} (n : ℕ) (hh : h ≤ h') (hr : r ≤ r')
    (he : re ≤ re') : -- --- CONCL ---
    ConZonotope.reduceCost n h r re ≤ ConZonotope.reduceCost n h' r' re' := by -- --- PROOF ---
  have := Cost.le_iff.mp (Zonotope.reduceGirardCost_mono n hh)
  simp only [ConZonotope.reduceCost, Cost.le_iff, Cost.ops_add]
  have g : 2 * (n * (1 + h)) + (r + re) * (h + 1) ≤ 2 * (n * (1 + h')) + (r' + re') * (h' + 1) := by
    gcongr
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
