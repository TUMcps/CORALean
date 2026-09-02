import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearEmbedding
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict

/-!
# What `NonlinearSys` guarantees

That it generalizes `LinearSys`, in `LinearEmbedding`, and that it reduces to
it again, in the others: `LinInputOuter` is where the certificate is spent,
`Linearize` turns a confined run into a linear one, and `ReachOuter` hands that
run to the linear reachability already proved.

`Restrict` is what makes the one-step forms possible: `linearize_horizon` asks
confinement on `[0, τ]` and gives back a linear run on `[0, τ]`, which is
conservative linearization as CORA runs it.

One linearization all the same. Re-linearizing along a horizon, and the
polynomialization variant, are not here.
-/
