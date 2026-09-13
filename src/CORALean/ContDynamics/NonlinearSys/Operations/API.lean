import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLin
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolySearch
import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatError
import CORALean.ContDynamics.NonlinearSys.Operations.RelinDeltaReach
import CORALean.ContDynamics.NonlinearSys.Operations.RelinReach
import CORALean.ContDynamics.NonlinearSys.Operations.RelinTimeInterval

/-!
# What a linearization computes

The two halves of one linearization: `Linearize` is the linear system, and
`LinInput` the set its input has to range over for the two to agree. Neither
mentions a derivative — what the split costs is an `AbstractionError`
certificate, not a bound on `f`. `PrecompStatError` is CORA's
`priv_precompStatError`, computing the second-order term instead of boxing it.

`RelinReach` is what a sequence of steps computes: one linear recursion step
per linearization, the set reached at a step's end the next one's initial set.
`RelinTimeInterval` is the same step over its whole interval; `RelinDeltaReach`
is CORA's `Rdiff`, how far a step moves from where it started.

`AbstrErrLin` is CORA's `priv_abstrerr_lin` at `tensorOrder = 2`: the error box a
second-order expansion leaves, data here and certified in `Theorems`.
`LagrangeRemainder` is the same one order up, once the quadratic term is
subtracted exactly rather than boxed.

`AbstrErrPolySearch` is `linReach`'s while loop for `alg = 'poly'`: a fuel-bounded
search over candidate applied errors, packaged into a `LinStep` the moment one is
accepted by the certificate already proved sufficient.
-/
