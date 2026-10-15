module

public import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfCheck
public import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfOutput
public import CORALean.ContDynamics.LinParamSysDT.Theorems.HoldsOfReach
public import CORALean.ContDynamics.LinParamSysDT.Theorems.NotHoldsOfSimulate
public import CORALean.ContDynamics.LinParamSysDT.Theorems.OutputOuter
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachEqToLinParam
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachBigO
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOneOuter
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOrderLe
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterInstances
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterOn
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachSetSubsetReach
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.LinParamSysDT.Theorems.SimulateMemReach
public import CORALean.ContDynamics.LinParamSysDT.Theorems.SimulateIsTrajectory
public import CORALean.ContDynamics.LinParamSysDT.Theorems.MemInputSet
public import CORALean.ContDynamics.LinParamSysDT.Theorems.IsTrajectoryCanonical
public import CORALean.ContDynamics.LinParamSysDT.Theorems.IsTrajectoryToLinParam

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
open re-expression question — a call this file does not make.

`SimulateTrajectory`/`SimulateMemReach` are `simulate` sampling one run, at a
matrix chosen per step, landing inside `reach` — same shape as `LinearSysDT`'s.
`NotHoldsOfSimulate` is the falsification corollary, mirroring `LinearSysDT`'s.
`ReachOrderLe`/`ReachBigO` carry the size bound over unchanged, and
`ReachSetSubsetReach`/`ReachUnionOuter` are what `Instances` needs.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/
