# hybridDynamics/@nonlinearReset

CORA methods of `hybridDynamics/@nonlinearReset/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NonlinearReset`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `derivatives` | out-of-scope | n/a — matlab-runtime |  |
| `eq` | out-of-scope | n/a — matlab-runtime |  |
| `evaluate` | proved | [`NonlinearReset.evaluate`](../../../src/CORALean/HybridDynamics/Operations/NonlinearResetEvaluate.lean), [`NonlinearReset.evaluate_toNonlinearReset`](../../../src/CORALean/HybridDynamics/Theorems/NonlinearResetEvaluateToNonlinearReset.lean) | numeric arguments only, `x_ = f(x, u)`; the set-valued evaluation, a Taylor expansion with a remainder over `J`, `H`, `T`, is not given; the theorem is agreement with `Transition.reset` at a point; scalar-free, no float counterpart |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `lift` | proved | [`NonlinearReset.lift`](../../../src/CORALean/HybridDynamics/Operations/NonlinearResetLift.lean), [`NonlinearReset.lift_evaluate_bind`](../../../src/CORALean/HybridDynamics/Theorems/NonlinearResetLiftBind.lean), [`NonlinearReset.lift_evaluate_of_not_mem`](../../../src/CORALean/HybridDynamics/Theorems/NonlinearResetLiftOfNotMem.lean) | `R^n → R^n` only, as in CORA; exact: at the bound coordinates (`stateBind` injective) the lifted reset is the old one applied to the bound state and input, and elsewhere it is the identity if `id` holds and `0` otherwise; scalar-free, no float counterpart |
| `ne` | out-of-scope | n/a — matlab-runtime |  |
| `nonlinearReset` | proved | [`NonlinearReset`](../../../src/CORALean/HybridDynamics/Definitions/NonlinearReset.lean), [`Transition.toNonlinearReset`](../../../src/CORALean/HybridDynamics/Operations/TransitionToNonlinearReset.lean), [`NonlinearReset.evaluate_toNonlinearReset`](../../../src/CORALean/HybridDynamics/Theorems/NonlinearResetEvaluateToNonlinearReset.lean) | the reset is the function `f(x, u)` itself, the dimensions are type indices and the derivative handles are not stored; the theorem says the affine reset of a `Transition` is one, at every point; scalar-free, so no float counterpart |
| `resolve` | — | — |  |
| `synchronize` | — | — |  |
