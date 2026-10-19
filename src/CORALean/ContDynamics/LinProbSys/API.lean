module

public import CORALean.ContDynamics.LinProbSys.Definitions.API
public import CORALean.ContDynamics.LinProbSys.LinProbSys
public import CORALean.ContDynamics.LinProbSys.Operations.API
public import CORALean.ContDynamics.LinProbSys.Theorems.API
public import CORALean.ContDynamics.LinProbSys.Counterexamples.API

/-!
# Linear systems with white noise, collected

The system in `LinProbSys`, CORA's `linProbSys`, the multivariate Ornstein-Uhlenbeck process
`ẋ = Ax + Bu + Cξ` at the real layer only, and its runs, `IsTrajectory`, given by the law of the
solution (a definition, not a theorem: the process driven by a Brownian motion is not defined).
`post` is its reach loop's step, on a probabilistic zonotope for the particular solution; what
it guarantees is the covariance recursion in `Theorems`, the covariance of the noise being
`noiseCovariance` of `LinearSys`. `initReach` is its first step with the input covariance
corrected: CORA's is the printed form of the paper, the drift `-A`'s, kept in `Operations` to
say so. For a run, `Theorems` proves the mean in `initReach`'s sets, the covariance of every
step, and the run in the time-point set of `initReach` with probability at least
`P[-γ ≤ N(0, 1) ≤ γ]ⁿ`; not for the time-interval set or `post`'s sets.
-/
