import CORALean.ContDynamics.OutputEq.Operations.API
import CORALean.ContDynamics.OutputEq.OutputEq
import CORALean.ContDynamics.OutputEq.Theorems.API

/-!
# Output equations, collected

The equation and what it computes on a point in `OutputEq`, the output set in
`Operations`, its guarantee in `Theorems`.

The one directory here that is not a system class. An output equation is paired
with a set rather than stored in a system, so it applies to every system in
`ContDynamics` at once — which is what a field on one of them would not do.
-/
