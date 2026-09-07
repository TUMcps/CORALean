import CORALean.ContDynamics.NonlinearSys.Theorems.ConfinedOfBall
import CORALean.ContDynamics.NonlinearSys.Theorems.ConfinementOfSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearEmbedding
import CORALean.ContDynamics.NonlinearSys.Theorems.TrajectoryIffNonlinearSys
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterHorizonInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetConfinementOfSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinReach
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinTimeInterval
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinTimeIntervalOfSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuterInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinTimeIntervalOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
import CORALean.ContDynamics.NonlinearSys.Theorems.Shift

/-!
# What `NonlinearSys` guarantees

That it generalizes `LinearSys`, in `LinearEmbedding`, and that it reduces to
it again, in the others: `LinInputOuter` spends the certificate, `Linearize`
turns a confined run into a linear one, `ReachOuter` hands that run to the
linear reachability already proved, and `Restrict` makes the one-step forms.

`Shift` and `RelinReachOuter` are the loop: a step is proved on a clock
starting at zero, so `Shift` re-anchors the run and `RelinReachOuter` chains
the steps, each step's enclosure becoming the next one's initial set.
`RelinTimeIntervalOuter` covers every time of a step, not only its ends.

`ConfinedOfBall` and `ConfinementOfSubset` pay off the confinement hypothesis
those carry per step: the run cannot cross a ball of radius `ρ > MΔt` about the
start of a step, so inflating the computed set and checking it discharges it.

The `ReachSet` files say that of the reachable set rather than of a run:
`ReachSetOuter` puts a run into it, `ReachSetConfinementOfSubset` confines it,
and the `ReachSetSubset` files enclose it — the last on the computed sets
alone.

The polynomialization variant, which propagates a `PolyZonotope` rather than
re-linearizing, is not here.
-/
