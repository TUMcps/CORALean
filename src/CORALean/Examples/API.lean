import CORALean.Examples.BackwardReach
import CORALean.Examples.BackwardReachExists
import CORALean.Examples.BallLocalityEnumerated
import CORALean.Examples.BouncingBall
import CORALean.Examples.BoundedHorizonInvariant
import CORALean.Examples.CapsuleObstacle
import CORALean.Examples.ConPolyZonoGuard
import CORALean.Examples.ConversionRoundTrip
import CORALean.Examples.ConvNet
import CORALean.Examples.ConvNetFloat
import CORALean.Examples.DependencyPreservation
import CORALean.Examples.DiscretizeWithEnclosedExp
import CORALean.Examples.DiscretizeWithMatZonotope
import CORALean.Examples.EllipsoidPlus
import CORALean.Examples.ExactSecondOrderExp
import CORALean.Examples.ExpOfIntervalMatrix
import CORALean.Examples.ExpRelaxGreedy
import CORALean.Examples.FeedForward
import CORALean.Examples.FeedForwardFloat
import CORALean.Examples.GuardCutThenReset
import CORALean.Examples.HPolytopePlus
import CORALean.Examples.LagrangeRemainder
import CORALean.Examples.LinearSysCheck
import CORALean.Examples.LinParamSysCheck
import CORALean.Examples.LinParamUncertainMatrix
import CORALean.Examples.MinkowskiDifference
import CORALean.Examples.NeurNetControl
import CORALean.Examples.NonlinearReachCheck
import CORALean.Examples.NonlinearSysDTReach
import CORALean.Examples.NonlinParamReachCheck
import CORALean.Examples.Polynomialization
import CORALean.Examples.PolyZonotopeReach
import CORALean.Examples.ReachFloat
import CORALean.Examples.ReachOrderStaysBounded
import CORALean.Examples.ReachSpecializations
import CORALean.Examples.ReductionAtReal
import CORALean.Examples.RotationFloat
import CORALean.Examples.RunnableFloat
import CORALean.Examples.SimulateAndFalsify
import CORALean.Examples.SoundCompression
import CORALean.Examples.UncertainGraphLocality
import CORALean.Examples.VerifyBySplitting
import CORALean.Examples.ZonoBundleIntersection

/-!
# Worked examples, collected

One per component, each at a concrete representation, and compiled with
everything else — so an instance that stops resolving fails the build rather
than waiting for someone to try the library. A library cannot notice that from
the inside; only a use site can.

`Demo.lean` is deliberately not collected here: it is a target of its own, an
executable that is run rather than a use site that is compiled.
`Bench.lean` is deliberately not collected here, for the same reason.
-/
