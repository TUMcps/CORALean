module

public import CORALean.ContDynamics.OutputEq.Theorems.HausdorffDist2EvalLe
public import CORALean.ContDynamics.OutputEq.Theorems.HoldsOfCheck
public import CORALean.ContDynamics.OutputEq.Theorems.HoldsOfOutputSet
public import CORALean.ContDynamics.OutputEq.Theorems.OutputSetNoiseOuter
public import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter

/-!
# What `OutputEq` guarantees

That `outputSet` contains the output of every state-input pair it was given, and
what checking a specification on it then buys. Neither names a system: the state
comes from whatever produced it.

`hausdorffDist₂_eval_le` is different in kind: not an over-approximation guarantee but an error
bound, at `‖·‖₂` rather than the supremum norm `outputSet_outer` is silent about — Wetzlinger et
al.'s Prop. 5, cited in its own file.
-/
