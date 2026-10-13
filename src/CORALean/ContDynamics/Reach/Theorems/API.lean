module

public import CORALean.ContDynamics.Reach.Theorems.HoldsOfCheck
public import CORALean.ContDynamics.Reach.Theorems.StepsSpec
public import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal

/-!
# What every `Reach` instance guarantees

`HoldsOfCheck`: a passed `Reach.check` — `reach` returned a set, and the
specification checked on it — is the specification on `reachExact`, once, for
every system class. `StepsSpec`: a step count `Reach.steps` returns spans the
horizon exactly; `StepsSpecToReal` the same at a float time step, in ℝ.
-/
