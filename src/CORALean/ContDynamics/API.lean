import CORALean.ContDynamics.LinearSys.API
import CORALean.ContDynamics.LinearSysDT.API

/-!
# Systems and their reachability, collected

One directory per system class. The algorithms are written against the `ContSet`
interfaces alone, so none names a representation. The `*Zonotope` theorems are
the exceptions: they say what is left once a representation that does have the
required properties is substituted in.
-/
