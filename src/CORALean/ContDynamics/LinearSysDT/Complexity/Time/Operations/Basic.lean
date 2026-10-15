module

public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# `ContDynamics/LinearSysDT/Complexity/Time/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- ===============================  `LinearSysDT.reachStepBound`  =============================== --
-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The same three costs at a step's worst case: `o * n` generators reaching
the `mtimes`, `o * n + hU` reaching the `reduce`. -/
def LinearSysDT.reachStepBound (n hU o : ℕ) : Cost :=
  Zonotope.mtimesCost n n (o * n) + Zonotope.plusCost n (o * n) hU
    + Zonotope.reduceGirardCost n (o * n + hU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
