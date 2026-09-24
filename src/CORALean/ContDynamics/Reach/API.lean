import CORALean.ContDynamics.Reach.Operations.API
import CORALean.ContDynamics.Reach.Reach
import CORALean.ContDynamics.Reach.Theorems.API

/-!
# The reachability interface, collected

`Reach` alone: every system's instance of it sits with that system, in its own
`Instances.lean`, rather than here — the class is shared, the instances are
not. `Operations` checks a specification on what `reach` returns, and
`Theorems` holds what follows for every instance at once.
-/
