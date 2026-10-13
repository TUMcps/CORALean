module

public import CORALean.ContDynamics.LinProbSys.Operations.InitReachCov
public import CORALean.ContDynamics.LinProbSys.Operations.Post
public import CORALean.ContDynamics.LinProbSys.Operations.EnclosingHull
public import CORALean.ContDynamics.LinProbSys.Operations.InputCov
public import CORALean.ContDynamics.LinProbSys.Operations.InitReach
public import CORALean.ContDynamics.LinProbSys.Operations.ReachCovCora

/-!
# What `LinProbSys` computes

`InitReach` is the first step of the probabilistic reach loop, `Post` every later one.
`InputCov` is the covariance of one step's noise `initReach` uses, CORA's with the sign of the
exponent corrected; `InitReachCov` is CORA's own, at a diagonal `A`, kept to say what CORA
computes and where it parts from the process, see `Theorems`.
-/
