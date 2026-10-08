import CORALean.ContDynamics.NonlinParamSys.Operations.Augment
import CORALean.ContDynamics.NonlinParamSys.Operations.ReachUnion
import CORALean.ContDynamics.NonlinParamSys.Operations.ReachFloat
import CORALean.ContDynamics.NonlinParamSys.Operations.ReachFloatChecked

/-!
# What `NonlinParamSys` computes

`Augment` is the parameter read as extra states with zero dynamics, CORA's
standard treatment; `ReachUnion` runs the augmented system's re-linearization
loop from `X₀ × P` and projects every member of the union back to the state.
-/
