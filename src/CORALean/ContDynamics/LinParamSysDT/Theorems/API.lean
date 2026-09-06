import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfOutput
import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfReach
import CORALean.ContDynamics.LinParamSysDT.Theorems.OutputOuter
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachEqToLinParam
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterInstances
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterOn
import CORALean.ContDynamics.LinParamSysDT.Theorems.ToLinParam
import CORALean.ContDynamics.LinParamSysDT.Theorems.TrajectoryToLinParam

/-!
# What `LinParamSysDT` guarantees

That `reach` contains every trajectory, exactly `LinearSysDT.Theorems` for a
system matrix that is a *set*: `reach_outer`, its step in isolation
`reach_one_outer`, the bounded-run case `reach_outer_on` it hands off to, and
`output_outer`/`holds_of_reach`/`holds_of_output`, the same three corollaries
`LinearSysDT` has, over a fresh output-equation scalar `𝕋`.

`ReachOuterInstances` is the payoff: `Mtimes` was already written against a
set of matrices, so `reach_outer` is proved once and instantiates at an
interval matrix (Althoff [1, §3.3.1]), a matrix zonotope (§3.3.2), a matrix
polytope (§3.3.3), and a point matrix — `LinearSysDT` again — with no
representation-specific proof.

`ToLinParam`/`TrajectoryToLinParam`/`ReachEqToLinParam` are the bridge:
`LinearSysDT` really is that point-matrix instantiation, evidence for #29's
open question of whether to re-express it through this instead — a call this
file does not make.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/
