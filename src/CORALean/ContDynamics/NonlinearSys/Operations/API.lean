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
certificate, not a bound on `f`.

`PrecompStatError` is CORA's `priv_precompStatError`, which the polynomialization
variant computes instead of boxing the second-order term.

`RelinReach` is what a sequence of them computes: one step of the linear
recursion per linearization, the set reached at the end of a step becoming the
initial set of the next. `RelinTimeInterval` is the same step, over its whole
interval rather than its end alone, and `RelinDeltaReach` is CORA's `Rdiff`: how
far that step moves from where it started, which is what `alg = 'poly'` measures
its next error on.
-/
