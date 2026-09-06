import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterInstances
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterOn

/-!
# What `LinParamSysDT` guarantees

That `reach` contains every trajectory, exactly `LinearSysDT.Theorems` for a
system matrix that is a *set*: `reach_outer`, its step in isolation
`reach_one_outer`, and the bounded-run case `reach_outer_on` it hands off to.

`ReachOuterInstances` is the payoff: `Mtimes` was already written against a set
of matrices, so `reach_outer` is proved once and instantiates at an interval
matrix (Althoff [1, §3.3.1]), a matrix zonotope (§3.3.2, strictly tighter, an
interval matrix having thrown away every correlation between entries), and a
point matrix — `LinearSysDT` again — with no representation-specific proof.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/
