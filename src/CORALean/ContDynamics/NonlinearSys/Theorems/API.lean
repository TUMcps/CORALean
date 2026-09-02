import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearEmbedding
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuter

/-!
# What `NonlinearSys` guarantees

That it generalizes `LinearSys`, in `LinearEmbedding`, and that it reduces to
it again, in the other three: `LinInputOuter` is where the certificate is
spent, `Linearize` turns a confined run into a linear one, and `ReachOuter`
hands that run to the linear reachability already proved.

One step, and one linearization. Re-linearizing along a horizon, and the
polynomialization variant, are not here.
-/
