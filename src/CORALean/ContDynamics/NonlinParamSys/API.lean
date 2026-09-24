import CORALean.ContDynamics.NonlinParamSys.Definitions.API
import CORALean.ContDynamics.NonlinParamSys.Instances
import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
import CORALean.ContDynamics.NonlinParamSys.Operations.API
import CORALean.ContDynamics.NonlinParamSys.Theorems.API

/-!
# Continuous-time nonlinear systems with uncertain parameters, collected

The system and its two trajectory readings in `NonlinParamSys`, the relation
between them and to the two neighbouring classes it embeds and is embedded by
in `Theorems`. Reachability is the augmented-state treatment: the parameter as
`q` states with zero dynamics, `Operations/Augment`, the `NonlinearSys` loop run
on that, and the result projected back, `Operations/ReachUnion`; `Instances`
is the `Reach` instance, for the constant-parameter reading only.
-/
