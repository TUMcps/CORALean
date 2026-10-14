module

public import CORALean.ContDynamics.NonlinDASys.Definitions.API
public import CORALean.ContDynamics.NonlinDASys.Instances
public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContDynamics.NonlinDASys.Operations.API
public import CORALean.ContDynamics.NonlinDASys.Theorems.API
public import CORALean.ContDynamics.NonlinDASys.Counterexamples.API

/-!
# Nonlinear differential-algebraic systems, collected

The system and its trajectories in `NonlinDASys`; the index-1 assumption, the reduced model
and the reachable set in `Definitions`; the local reduction an index-1 system admits, the
correspondence of trajectories with the reduced ordinary system and the outer guarantee in
`Theorems`. Two routes to a reachable set: CORA's own, `linReach` and `initReach`, which
linearize the differential-algebraic system with an error term for the algebraic variable
(real layer, the error's sign corrected); and the reduced system's re-linearization loop,
`reachUnion` and `reachFloat`, which needs the reduced model as data and runs in floats.
-/
