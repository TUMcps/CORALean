import CORALean.ContDynamics.LinearARX.Definitions.GO
import CORALean.ContDynamics.LinearARX.LinearARX
import CORALean.ContDynamics.LinearARX.Definitions.API
import CORALean.ContDynamics.LinearARX.Operations.API
import CORALean.ContDynamics.LinearARX.Theorems.API

/-!
# Linear ARX models, collected

The model and its trajectories in `LinearARX`, the conversion to `LinearSysDT` in
`Operations`, and in `Theorems` that every ARX trajectory is one of the converted
system, so that its reach encloses the ARX outputs.

`Definitions` holds the exact ARMAX reachable sets, which `Theorems` shows the two
algorithms of the ARMAX paper compute (`tvp` is their parametrization). Left: a
representation-level ARX reach, the converse of the trajectory correspondence.
-/
