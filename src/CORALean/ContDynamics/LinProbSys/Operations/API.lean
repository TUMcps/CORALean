import CORALean.ContDynamics.LinProbSys.Operations.InitReachCov
import CORALean.ContDynamics.LinProbSys.Operations.Post
import CORALean.ContDynamics.LinProbSys.Operations.EnclosingHull

/-!
# What `LinProbSys` computes

`Post` is one step of the probabilistic reach loop. `InitReachCov` is the covariance
`initReach` assigns to the probabilistic input solution, at a diagonal `A`, kept to say what
CORA computes and where it parts from the process, see `Theorems`.
-/
