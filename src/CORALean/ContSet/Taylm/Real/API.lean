import CORALean.ContSet.Taylm.Real.Definitions.API
import CORALean.ContSet.Taylm.Real.Taylm
import CORALean.ContSet.Taylm.Real.Operations.API
import CORALean.ContSet.Taylm.Real.Theorems.API

/-!
# Taylor models, collected

The representation in `Taylm`, what a model means beyond it in `Definitions`, the operations
in `Operations` and their guarantees in `Theorems`. No interface instances: `plus` and `times`
act on functions over shared variables, not on range sets, so neither is a Minkowski `Plus`.
-/
