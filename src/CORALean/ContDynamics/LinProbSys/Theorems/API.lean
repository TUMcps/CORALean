import CORALean.ContDynamics.LinProbSys.Theorems.InitReachCovLt
import CORALean.ContDynamics.LinProbSys.Theorems.NoiseCovarianceAdd
import CORALean.ContDynamics.LinProbSys.Theorems.PostCov
import CORALean.ContDynamics.LinProbSys.Theorems.EnclosingHullCov
import CORALean.ContDynamics.LinProbSys.Theorems.InputCovEq
import CORALean.ContDynamics.LinProbSys.Theorems.InitReachInputCov
import CORALean.ContDynamics.LinProbSys.Theorems.InitReachPostCov
import CORALean.ContDynamics.LinProbSys.Theorems.InitReachTiOuter
import CORALean.ContDynamics.LinProbSys.Theorems.InitReachTpOuter

/-!
# What `LinProbSys` guarantees

`NoiseCovarianceAdd` is the covariance of the noise over two steps, `PostCov` that `post`'s
recursion carries it exactly. `InitReachCovLt` says CORA's own input covariance is below the
true one for an unstable system; `InputCovEq` that the corrected one is the true one,
`InitReachInputCov` and `InitReachPostCov` that `initReach` hands `post` exactly that, and
`InitReachTiOuter`, `InitReachTpOuter` that `initReach`'s sets enclose the means.
-/
