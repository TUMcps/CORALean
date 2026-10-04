import CORALean.ContDynamics.LinProbSys.Theorems.InitReachCovLt
import CORALean.ContDynamics.LinProbSys.Theorems.NoiseCovarianceAdd
import CORALean.ContDynamics.LinProbSys.Theorems.PostCov

/-!
# What `LinProbSys` guarantees

`NoiseCovarianceAdd` is the covariance of the noise over two steps, `PostCov` that `post`'s
recursion carries it exactly. `InitReachCovLt` says `initReach`'s own input covariance is
below the true one for an unstable system.
-/
