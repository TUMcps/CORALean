import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfHessian
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfLagrange
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfPoly
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrLinCenterSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrMono
import CORALean.ContDynamics.NonlinearSys.Theorems.GainOrderEqTopIff
import CORALean.ContDynamics.NonlinearSys.Theorems.GlobalAbstrErrEqLocalAbstrErr
import CORALean.ContDynamics.NonlinearSys.Theorems.LagrangeRemainderMono
import CORALean.ContDynamics.NonlinearSys.Theorems.ConfinedOfBall
import CORALean.ContDynamics.NonlinearSys.Theorems.ConfinementOfSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearEmbedding
import CORALean.ContDynamics.NonlinearSys.Theorems.TrajectoryIffNonlinearSys
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.PolyAbstractionErrorGetSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.PolyAbstractionErrorOfQuadRemainder
import CORALean.ContDynamics.NonlinearSys.Theorems.PrecompStatErrorPoint
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterHorizonInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachOuterInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetConfinementOfSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinReach
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinTimeInterval
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinTimeIntervalHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinTimeIntervalOfSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinDeltaReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuterInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinTimeIntervalOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
import CORALean.ContDynamics.NonlinearSys.Theorems.Shift
import CORALean.ContDynamics.NonlinearSys.Theorems.VarInputsMono
import CORALean.ContDynamics.NonlinearSys.Theorems.VarInputsOuter

/-!
# What `NonlinearSys` guarantees

That it generalizes `LinearSys`, in `LinearEmbedding`, and that it reduces to
it again: `LinInputOuter` spends the certificate, `Linearize` turns a confined
run linear, `ReachOuter` hands it on, and `Restrict` makes the one-step forms.
`Shift` and `RelinReachOuter` are the loop: a step is proved on a clock starting
at zero, so `Shift` re-anchors the run and `RelinReachOuter` chains the steps.
`RelinTimeIntervalOuter` covers a step's interval; `RelinDeltaReachOuter` spans.

`ConfinedOfBall` and `ConfinementOfSubset` pay off the confinement hypothesis
those carry per step: the run cannot cross a ball of radius `ρ > MΔt` about a
step's start, so inflating the computed set and checking it discharges it. The
`ReachSet` files say that of the reachable set rather than of a run:
`ReachSetOuter` puts a run into it, and the `ReachSetSubset` files enclose it.

`AbstractionErrorOfHessian` is one supplier, `AbstrErrLinCenterSubset` minimises
what it gives at the centre, `AbstractionErrorOfLagrange` is the same one order
up, and the `PolyAbstractionError` files are the polynomialization variant's:
`OfQuadRemainder` builds one, `GetSubset` splits it, `...OfPoly` forgets the
dependency. The `Mono` files are what a dependency argument asks instead.
`GlobalAbstrErrEqLocalAbstrErr` is what it costs to read a step's accumulated
error as its local one — Rådström cancellation — and `GainOrderEqTopIff` is what
the gain order is for: an infinite order is a method that abstracts exactly.
-/
