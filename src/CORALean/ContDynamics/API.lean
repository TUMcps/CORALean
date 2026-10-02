import CORALean.ContDynamics.LinearARX.API
import CORALean.ContDynamics.NonlinearARX.API
import CORALean.ContDynamics.LinearSys.API
import CORALean.ContDynamics.LinearSysDT.API
import CORALean.ContDynamics.LinParamSys.API
import CORALean.ContDynamics.LinParamSysDT.API
import CORALean.ContDynamics.NeurNetContrSys.API
import CORALean.ContDynamics.NeurNetContrSysDT.API
import CORALean.ContDynamics.NonlinDASys.API
import CORALean.ContDynamics.NonlinParamSys.API
import CORALean.ContDynamics.NonlinearSys.API
import CORALean.ContDynamics.NonlinearSysDT.API
import CORALean.ContDynamics.OutputEq.API
import CORALean.ContDynamics.Reach.API

/-!
# Systems and their reachability, collected

One directory per system class, and `OutputEq`, which is not one. The algorithms
are written against the `ContSet` interfaces alone, so none names a
representation, and they sit in `CORALean`, in neither arithmetic layer. The
`*Zonotope` and `*ConZonotope` theorems are the exceptions: they say what is
left once a representation that does have the required properties is put in.

`OutputEq` is CORA's `y = C x + D u`, kept out of the system classes so that it
applies to all of them: paired with a reachable set and an input set at the point
of use, which is what lets a sampled system read `u` from the set its run was
described by rather than from the one its discretization steps with.

`LinearARX` converts to `LinearSysDT`, `NonlinearSys` hands a confined run to `LinearSys`
by conservative linearization. The two closed loops compute nothing of their own, and are
the only directories reaching outside `ContDynamics`, the input set being what `NN` encloses.

`Reach` is the shared reachability class every system below instantiates where
it fits. `NonlinearSys` and `NonlinearSysDT` do, bundled with their linearizations,
their `reach` returning `none` where a run-time test cannot confirm the
confinement the linearizations assume; `NonlinDASys` through `NonlinearSys`, its algebraic
variable eliminated by a supplied reduced model; `NonlinParamSys` through `NonlinearSys`, its
parameter an extra state, for the constant-parameter reading.
-/
