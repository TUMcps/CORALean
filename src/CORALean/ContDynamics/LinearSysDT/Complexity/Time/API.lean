module

public import CORALean.ContDynamics.LinearSysDT.Complexity.Time.Operations.API
public import CORALean.ContDynamics.LinearSysDT.Complexity.Time.Theorems.API

/-!
# What running `LinearSysDT.reach` costs

The worked composition the rest of `Complexity/Time/` exists for.
`Operations/ReachCost.lean` says which operations a step runs and at what sizes, its
recursion mirroring `Operations.lean` line for line. `Theorems/ReachCostLe.lean` proves the
run's cost is at most `k` worst-case steps, out of the per-operation counts in
`ContSet/Zonotope/Real/Complexity/Time/` and the generator-count bound `reach_order_le` in
`Theorems/`; nothing in it is asserted. `Theorems/ReachStepBoundIsBigO.lean` reads a step
off as `O(n ^ 3)`.

The bound is stated at `𝒵` and `𝕋 = ℝ`, not at the classes `reach` is written
against: `plus` and `reduce` cost what a representation makes them cost, so a
cost belongs where the instance is. The same three costs at `Interval`'s
counts would give a run with no reduction term at all.

That is the shape a whole algorithm's `O` is assembled in: a size fact per
operation, a cost per operation, monotonicity to join them, induction over the
loop, and `IsBigO` last and only to present one parameter's slice.
-/
