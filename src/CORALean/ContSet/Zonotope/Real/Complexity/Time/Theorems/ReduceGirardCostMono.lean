module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost

@[expose] public section

/-!
# `Zonotope.reduceGirardCost_mono`

Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost.

## Inputs
* `h` – smaller generator count
* `h'` – larger generator count
* `n` – dimension

## Hypotheses
* `hle` – generator counts ordered

## Conclusion
* cost is monotone in the generator count
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.reduceGirardCost_mono {h h' : ℕ} (n : ℕ) (hle : h ≤ h') :
    Zonotope.reduceGirardCost n h ≤ Zonotope.reduceGirardCost n h' := by
  refine Cost.add_le_add (Cost.add_le_add ?_ ?_) (Zonotope.reduceByCost_mono n hle hle)
  · exact Nat.mul_le_mul_right _ hle
  · exact Cost.sort_mono hle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
