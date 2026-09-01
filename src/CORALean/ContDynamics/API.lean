import CORALean.ContDynamics.LinearSys.API
import CORALean.ContDynamics.LinearSysDT.API
import CORALean.ContDynamics.NonlinearSys.API

/-!
# Systems and their reachability, collected

One directory per system class. The algorithms are written against the `ContSet`
interfaces alone, so none names a representation. The `*Zonotope` and
`*ConZonotope` theorems are the exceptions: they say what is left once a
representation that does have the required properties is substituted in.

`NonlinearSys` so far holds only the representation and what a trajectory of it
is; it has no reachability yet.
-/
