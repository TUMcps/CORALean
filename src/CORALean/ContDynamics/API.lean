import CORALean.ContDynamics.LinearSys.API
import CORALean.ContDynamics.LinearSysDT.API
import CORALean.ContDynamics.NonlinearSys.API

/-!
# Systems and their reachability, collected

One directory per system class. The algorithms are written against the `ContSet`
interfaces alone, so none names a representation. The `*Zonotope` and
`*ConZonotope` theorems are the exceptions: they say what is left once a
representation that does have the required properties is substituted in.

`NonlinearSys` computes nothing of its own: conservative linearization hands a
confined run to `LinearSys`, so every reachability guarantee in the directory is
a linear one applied to a widened input set.
-/
