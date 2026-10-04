import CORALean.ContDynamics.LinearARX.Definitions.GO
import CORALean.ContDynamics.LinearARX.LinearARX
import CORALean.ContDynamics.LinearARX.Operations.API
import CORALean.ContDynamics.LinearARX.Theorems.API

/-!
# Linear ARX models, collected

The model and its trajectories in `LinearARX`, the conversion to `LinearSysDT` in
`Operations`, and in `Theorems` that every ARX trajectory is one of the converted
system, so that its reach encloses the ARX outputs.

Left: ARX-form reach, its containment in the reach after conversion (the
conversion repeats each output in `p` windows and loses that dependency), the
converse of the trajectory correspondence, and `tvp`.
-/
