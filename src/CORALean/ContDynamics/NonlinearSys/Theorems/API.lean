import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearEmbedding
import CORALean.ContDynamics.NonlinearSys.Theorems.TrajectoryIffNonlinearSys
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterHorizonInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuterInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
import CORALean.ContDynamics.NonlinearSys.Theorems.Shift

/-!
# What `NonlinearSys` guarantees

That it generalizes `LinearSys`, in `LinearEmbedding`, and that it reduces to
it again, in the others: `LinInputOuter` is where the certificate is spent,
`Linearize` turns a confined run into a linear one, and `ReachOuter` hands that
run to the linear reachability already proved.

`Restrict` is what makes the one-step forms possible: `linearize_horizon` asks
confinement on `[0, τ]` and gives back a linear run on `[0, τ]`, which is
conservative linearization as CORA runs it.

`Shift` and `RelinReachOuter` are the loop. A step is proved on a clock starting
at zero, so `Shift` re-anchors the run and `RelinReachOuter` chains the steps by
induction on the step count, each step's enclosure becoming the next one's
initial set. Confinement stays a hypothesis per step, on that step's window
alone.

The polynomialization variant, which propagates a `PolyZonotope` rather than
re-linearizing, is not here.
-/
