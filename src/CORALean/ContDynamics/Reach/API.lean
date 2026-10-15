module

public import CORALean.ContDynamics.Reach.Definitions.API
public import CORALean.ContDynamics.Reach.Operations.API
public import CORALean.ContDynamics.Reach.Theorems.API

/-!
# The reachability interface, collected

What goes with `Reach`, whose class is in `ContDynamics/Interfaces.lean`: every system's instance of
it sits with that system, in its own `Instances.lean` — the class is shared, the instances are not.
`Definitions` is how a reach operation takes its arguments, CORA's `params`/`options` split;
`Operations` checks a specification on what `reach` returns, and `Theorems` holds what follows for
every instance at once.
-/
