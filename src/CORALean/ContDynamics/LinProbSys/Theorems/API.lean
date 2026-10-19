module

public import CORALean.ContDynamics.LinProbSys.Theorems.InitReachCovLt
public import CORALean.ContDynamics.LinProbSys.Theorems.NoiseCovarianceAdd
public import CORALean.ContDynamics.LinProbSys.Theorems.PostCov
public import CORALean.ContDynamics.LinProbSys.Theorems.EnclosingHullCov
public import CORALean.ContDynamics.LinProbSys.Theorems.InputCovEq
public import CORALean.ContDynamics.LinProbSys.Theorems.InitReachInputCov
public import CORALean.ContDynamics.LinProbSys.Theorems.InitReachPostCov
public import CORALean.ContDynamics.LinProbSys.Theorems.InitReachTiOuter
public import CORALean.ContDynamics.LinProbSys.Theorems.InitReachTpOuter
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryAEMeasurable
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryIntegral
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryCovariance
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryZonotopeProb
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryMeanSplit
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryInitReachTpMean
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryInitReachTiMean
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryInitReachTpProb
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryInitReachPostCov

/-!
# What `LinProbSys` guarantees

`NoiseCovarianceAdd` is the covariance of the noise over two steps, `PostCov` that `post`'s
recursion carries it exactly. `InitReachCovLt` says CORA's own input covariance is below the
true one for an unstable system; `InputCovEq` that the corrected one is the true one,
`InitReachInputCov` and `InitReachPostCov` that `initReach` hands `post` exactly that, and
`InitReachTiOuter`, `InitReachTpOuter` that `initReach`'s sets enclose the means.

The runs, `IsTrajectory`, are given by their law, the Gaussian of the solution, a definition
and not a theorem (see the main file). `IsTrajectoryIntegral` and `IsTrajectoryCovariance` read
off a run's mean and covariance `Σ_s(t)`; `IsTrajectoryInitReachTpMean` and
`IsTrajectoryInitReachTiMean` put the mean in `initReach`'s sets, `IsTrajectoryInitReachPostCov`
puts the covariance of every `post` step on the run's. `IsTrajectoryZonotopeProb` and
`IsTrajectoryInitReachTpProb` are the probabilistic guarantee: a run is in the `γ`-confidence
set of its probabilistic zonotope, and in `initReach`'s time-point set, with probability at least
`P[-γ ≤ N(0, 1) ≤ γ]ⁿ`. Not proved: the same for the time-interval set and for `post`'s sets.
-/
