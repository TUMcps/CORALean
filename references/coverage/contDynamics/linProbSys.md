# contDynamics/@linProbSys

CORA methods of `contDynamics/@linProbSys/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** [`LinProbSys`](../../../src/CORALean/ContDynamics/LinProbSys/LinProbSys.lean) (real layer only).

| Method | State | In CORALean | Note |
|---|---|---|---|
| `display` | out-of-scope | n/a — plotting/display |  |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `getfcn` | out-of-scope | n/a — matlab-runtime |  |
| `initReach` | — | — | cora-issue — `priv_inputSolution` takes the noise covariance of one step as `V Σ Vᵀ`, `Σ_ij = D_ij/(λ_i + λ_j) (1 − e^{−(λ_i+λ_j) r})`, which is the one for the drift `−A` (the printed formula of the ECC 2009 paper, FINDINGS.md): `LinProbSys.initReachCov` is that at a diagonal `A` and is below the true covariance `(e² − 1)/2` at `A = C = r = 1` (`LinProbSys.initReachCov_lt_noiseCovariance`); the probabilistic zonotope `post` carries is then too narrow for an unstable `A`. Not defined here beyond that covariance, and the deterministic part (`pexpm`, `tie`, the input solution) has no theorem |
| `linProbSys` | proved | [`LinProbSys`](../../../src/CORALean/ContDynamics/LinProbSys/LinProbSys.lean), [`noiseCovariance_add`](../../../src/CORALean/ContDynamics/LinProbSys/Theorems/NoiseCovarianceAdd.lean) | real layer only (a Gaussian process has no float counterpart). The system is the matrices `A`, `B`, `C` (`C` square, as `inputArgsCheck` asks); the stochastic process is not defined, its law's noise part being `noiseCovariance A C t` (`LinearSys`), and the theorem is that covariance over two steps, `Σ(s + t) = e^{As} Σ(t) e^{Aᵀs} + Σ(s)`, exact, entry by entry |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `post` | proved | [`LinProbSys.post`](../../../src/CORALean/ContDynamics/LinProbSys/Operations/Post.lean), [`LinProbSys.post_cov`](../../../src/CORALean/ContDynamics/LinProbSys/Theorems/PostCov.lean) | partial: the covariance, exact, real layer (`noncomputable`: the matrix exponential), not float. `post` carries `Rhom`, `Rpar_det`, `Raux_det` by `eAt` (and the box of `Raux_det` onto `Rpar_det`) and `Rpar_prob` by `eAt Rpar_prob + pRinput`; with `pRinput` the covariance of one step and `Rpar_prob` that of `T`, the returned one, and the time-interval set's, is the noise covariance of `Δt + T`. The sets `Rhom`, `Rpar_det`, `Raux_det` and the means have no theorem, and no claim that the probabilistic zonotope encloses the law of the process: `pRinput` is `initReach`'s, which is not sound |
| `simulate` | out-of-scope | n/a — random/sampling | draws `mvnrnd(mu,Sigma)` as the noise input at every step |
