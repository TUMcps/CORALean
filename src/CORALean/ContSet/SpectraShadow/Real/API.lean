import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
import CORALean.ContSet.SpectraShadow.Real.Definitions.API
import CORALean.ContSet.SpectraShadow.Real.Operations.API
import CORALean.ContSet.SpectraShadow.Real.Theorems.API
import CORALean.ContSet.SpectraShadow.Real.Instances
import CORALean.ContSet.SpectraShadow.Real.Theorems.EncloseExact

/-!
# Spectrahedral shadows, collected

The representation in `SpectraShadow`, the operations in `Operations`, their
guarantees in `Theorems`, and the class instances in `Instances`. No `Complexity`
or `Cost`: every operation here rewrites its fields without arithmetic, so there
is no running cost to assert beyond the size of what it builds.
-/
