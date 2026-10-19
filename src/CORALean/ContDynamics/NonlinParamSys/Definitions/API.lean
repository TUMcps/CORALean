module

public import CORALean.ContDynamics.NonlinParamSys.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinParamSys.Definitions.PancakeScaled
public import CORALean.ContDynamics.NonlinParamSys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NonlinParamSys.Definitions.WithSteps

/-!
# What `NonlinParamSys` means beyond the system itself

`WithSteps` bundles the system with its parameter set and the data a `Reach`
run of its augmented system spends; `ReachUnionExact` is the constant-parameter
reachable set that run encloses.
-/
