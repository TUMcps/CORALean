module

public import CORALean.ContDynamics.NonlinParamSys.Operations.Augment
public import CORALean.ContDynamics.NonlinParamSys.Operations.Linearize
public import CORALean.ContDynamics.NonlinParamSys.Operations.LinearizeFloat
public import CORALean.ContDynamics.NonlinParamSys.Operations.LinReachCora
public import CORALean.ContDynamics.NonlinParamSys.Operations.ReachUnion
public import CORALean.ContDynamics.NonlinParamSys.Operations.ReachFloat
public import CORALean.ContDynamics.NonlinParamSys.Operations.ReachFloatChecked

/-!
# What `NonlinParamSys` computes

`Augment` is the parameter read as extra states with zero dynamics, CORA's
standard treatment; `ReachUnion` runs the augmented system's re-linearization
loop from `X₀ × P` and projects every member of the union back to the state. `Linearize` is
CORA's parametric linearization, the matrix zonotopes of the Jacobians over the parameter box.
-/
