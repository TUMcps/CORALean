import CORALean.ContDynamics.NonlinearSysDT.Cost.Reach
import CORALean.ContDynamics.NonlinearSysDT.Cost.ReachBound

/-!
# What running `NonlinearSysDT.reach` costs

The second worked composition, and the one that shows the arrangement nests.
`LinearSysDT/Cost/` assembles an algorithm's bound out of per-operation counts;
this directory assembles an algorithm's bound out of *that algorithm*, used
whole at one step, and never reaches past it to a leaf count.

`Reach.lean` says which run a step is and at what sizes, its recursion
mirroring `Operations.lean` line for line. `ReachBound.lean` proves the run
costs at most `k` worst-case linear steps, and the bound it proves that against
is `LinearSysDT.reachStepBound` itself rather than a number of its own: a
re-linearized step runs the same three operations, so it costs the same.

What re-linearization does add is a hypothesis. Each step gets its own input
set from `linInput`, so the caller supplies one `hU` bounding all of them; with
uniform abstraction errors that is the linear statement unchanged.

No `IsBigO` here. It would be `LinearSysDT.reachStepBound_isBigO` again, at the
same `O(n ^ 3)`, and saying it twice would not make it truer.
-/
