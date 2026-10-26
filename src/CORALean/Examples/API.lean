import CORALean.Examples.AdaptiveReachFloat
import CORALean.Examples.AndEmptyFullspace
import CORALean.Examples.AndLevelSetFloat
import CORALean.Examples.AndPolygonFloat
import CORALean.Examples.AndZonotopeFloat
import CORALean.Examples.BackwardReach
import CORALean.Examples.BackwardReachExists
import CORALean.Examples.BallLocalityEnumerated
import CORALean.Examples.BouncingBall
import CORALean.Examples.BouncingBallFloat
import CORALean.Examples.BouncingBallUseSites
import CORALean.Examples.BoundedHorizonInvariant
import CORALean.Examples.CapsuleObstacle
import CORALean.Examples.ConPolyZonoGuard
import CORALean.Examples.ConZonotopeReduceKeep
import CORALean.Examples.ConZonotopeBoundFloat
import CORALean.Examples.ConZonotopeDisjointFloat
import CORALean.Examples.ZonoBundleBoundLPFloat
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
import CORALean.Examples.FixedPointDemo
import CORALean.Examples.FullDimRankFloat
import CORALean.Examples.ConZonotopeCertFloat
import CORALean.Examples.ZonoBundleCertFloat
import CORALean.Examples.ZonotopeContainsFloat
import CORALean.Examples.GuardCutThenReset
import CORALean.Examples.HPolytopePlus
import CORALean.Examples.IEEERounding
import CORALean.Examples.IsequalFloat
import CORALean.Examples.LagrangeRemainder
import CORALean.Examples.LevelSetCellFloat
import CORALean.Examples.LevelSetContainsFloat
import CORALean.Examples.LevelSetEmptyFloat
import CORALean.Examples.LinearARXReach
import CORALean.Examples.LinearSysCheck
import CORALean.Examples.LinearSysInputCheck
import CORALean.Examples.LinParamSysCheck
import CORALean.Examples.LinParamSysInputCheck
import CORALean.Examples.LinParamUncertainMatrix
import CORALean.Examples.LinProbSysNoise
import CORALean.Examples.MaxBackReachOracle
import CORALean.Examples.MinkDiffHPolytope
import CORALean.Examples.MinkDiffInterval
import CORALean.Examples.MinkDiffZonotope
import CORALean.Examples.NeurNetControl
import CORALean.Examples.NeurNetControlDT
import CORALean.Examples.NonlinDASysFloat
import CORALean.Examples.NonlinearARXFloat
import CORALean.Examples.NonlinearReachCheck
import CORALean.Examples.NonlinearSysDTReach
import CORALean.Examples.NonlinParamReachCheck
import CORALean.Examples.ParallelTwoComponents
import CORALean.Examples.ParallelSync
import CORALean.Examples.Polynomialization
import CORALean.Examples.PolyZonotopeReach
import CORALean.Examples.ReachFloat
import CORALean.Examples.ReachClosedLoopFloat
import CORALean.Examples.ReachHybridFloat
import CORALean.Examples.ReachOrderStaysBounded
import CORALean.Examples.ReachSpecializations
import CORALean.Examples.ReductionAtReal
import CORALean.Examples.RotationFloat
import CORALean.Examples.RotationInputFloat
import CORALean.Examples.RunnableFloat
import CORALean.Examples.SetIntersectionFloat
import CORALean.Examples.SimulateAndFalsify
import CORALean.Examples.EnclosesCompression
import CORALean.Examples.Interfaces
import CORALean.Examples.TaylmFloat
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
`BenchFlint.lean` is deliberately not collected here, for the same reason.
`BenchFlintMain.lean` is deliberately not collected here, for the same reason.
`Oracle.lean` is deliberately not collected here, for the same reason.
`HardwareCheck.lean` is deliberately not collected here, for the same reason.
`FlintCheck.lean` is deliberately not collected here, for the same reason.
`RunCheck.lean` is deliberately not collected here, for the same reason.
-/
