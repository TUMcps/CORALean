import CORALean.ContDynamics.LinearSys.Krylov.Definitions.API
import CORALean.ContDynamics.LinearSys.Krylov.Operations.API
import CORALean.ContDynamics.LinearSys.Krylov.Theorems.API

/-!
# Reachability in the Krylov subspace, collected

Althoff (TAC 2020) replaces `e^{At}v` by its Arnoldi approximation and carries the
approximation error as a box. Everything here is at ℝ and takes the a-posteriori error bound
the paper cites as a hypothesis.
-/
