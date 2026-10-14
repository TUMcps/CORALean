module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.SpectraShadow.Real.Definitions.API
public import CORALean.ContSet.SpectraShadow.Real.Operations.API
public import CORALean.ContSet.SpectraShadow.Real.Theorems.API
public import CORALean.ContSet.SpectraShadow.Real.Counterexamples.API
public import CORALean.ContSet.SpectraShadow.Real.Instances
public import CORALean.ContSet.SpectraShadow.Real.Theorems.EncloseExact

/-!
# Spectrahedral shadows, collected

The representation in `SpectraShadow`, the operations in `Operations`, their
guarantees in `Theorems`, and the class instances in `Instances`.
No `Complexity`: every operation here rewrites its fields without
arithmetic, so there is no running cost to assert beyond the size of what it
builds.
-/
