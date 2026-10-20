module

public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.Global.Cost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesIntervalMatCost

@[expose] public section

/-!
# `Zonotope.mtimesIntervalMatCost_mono`

Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost.

## Inputs
* `h` – smaller generator count
* `h'` – larger generator count
* `m` – matrix row count
* `n` – matrix column count

## Hypotheses
* `hh` – generator counts ordered

## Conclusion
* cost is monotone in the generator count
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Zonotope.mtimesIntervalMatCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    Zonotope.mtimesIntervalMatCost m n h ≤
      Zonotope.mtimesIntervalMatCost m n h' := by
  cost_mono [Zonotope.mtimesIntervalMatCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
