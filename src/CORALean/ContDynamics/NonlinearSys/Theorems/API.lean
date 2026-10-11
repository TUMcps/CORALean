import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrLinCenterSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrLoopFixed
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrMono
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrPolySearchEqSome
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfHessian
import CORALean.ContDynamics.NonlinearSys.Theorems.TaylorLagrangeSegment
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfLagrange
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorOfPoly
import CORALean.ContDynamics.NonlinearSys.Theorems.AdaptStepInvariant
import CORALean.ContDynamics.NonlinearSys.Theorems.BoxDiameterAbstrSolInf
import CORALean.ContDynamics.NonlinearSys.Theorems.ConfinedOfBall
import CORALean.ContDynamics.NonlinearSys.Theorems.ConfinementOfSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.EstimateGainBracket
import CORALean.ContDynamics.NonlinearSys.Theorems.GainDimLePow
import CORALean.ContDynamics.NonlinearSys.Theorems.GainDimTendstoPow
import CORALean.ContDynamics.NonlinearSys.Theorems.GainDimTendstoPowConst
import CORALean.ContDynamics.NonlinearSys.Theorems.GainOrderEqTopIff
import CORALean.ContDynamics.NonlinearSys.Theorems.GainOrderMaxCounterexample
import CORALean.ContDynamics.NonlinearSys.Theorems.GlobalAbstrErrEqLocalAbstrErr
import CORALean.ContDynamics.NonlinearSys.Theorems.GlobalAbstrErrLeLocalAbstrErr
import CORALean.ContDynamics.NonlinearSys.Theorems.GlobalAbstrErrLeLocalAbstrErrOfSolver
import CORALean.ContDynamics.NonlinearSys.Theorems.GlobalAbstrErrStepOfSolver
import CORALean.ContDynamics.NonlinearSys.Theorems.LagrangeRemainderMono
import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachPolyOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachPolyRegion
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearEmbedding
import CORALean.ContDynamics.NonlinearSys.Theorems.Linearize
import CORALean.ContDynamics.NonlinearSys.Theorems.LinearizeHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.OptDeltatDescent
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
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetEvalOn
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinTimeInterval
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinTimeIntervalHorizon
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetRelinTimeIntervalOfSubset
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinDeltaReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachOuterInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinReachEvalOn
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinTimeIntervalOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
import CORALean.ContDynamics.NonlinearSys.Theorems.RowNormExpansionOfAnalytic
import CORALean.ContDynamics.NonlinearSys.Theorems.RowNormExpansionCounterexample
import CORALean.ContDynamics.NonlinearSys.Theorems.Shift
import CORALean.ContDynamics.NonlinearSys.Theorems.SubsetAbstrReach
import CORALean.ContDynamics.NonlinearSys.Theorems.SubsetCentreAbstrReach
import CORALean.ContDynamics.NonlinearSys.Theorems.ClassicalTrajectoryIffNonlinearSys
import CORALean.ContDynamics.NonlinearSys.Theorems.TuneDeltatInitGain
import CORALean.ContDynamics.NonlinearSys.Theorems.VarInputsMono
import CORALean.ContDynamics.NonlinearSys.Theorems.VarInputsOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.VarInputsEqCounterexample
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.EnclosesOfHasFDerivAt
import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RegionFloatConfined
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinRunAtFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinRunFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinStepAtFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.RelinStepFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.SlopeRemainderAbstractionError
import CORALean.ContDynamics.NonlinearSys.Theorems.AbstrErrPolyFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.VarInputsFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.HessRemainderAbstractionError
import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachRunFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.OneStepFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachAlgFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachAlgFloatCheckedEqSome
import CORALean.ContDynamics.NonlinearSys.Theorems.AdmissibleLinErrorNotSufficient
import CORALean.ContDynamics.NonlinearSys.Theorems.ErrReachSubsetOfAbsLe
import CORALean.ContDynamics.NonlinearSys.Theorems.SplitReachOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.IdentifyCandidateFit
import CORALean.ContDynamics.NonlinearSys.Theorems.IdentifyLeCandidate
import CORALean.ContDynamics.NonlinearSys.Theorems.ReachFloatCheckedEqSome
import CORALean.ContDynamics.NonlinearSys.Theorems.OrderStepFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.ZonotopeRadiusAttained
import CORALean.ContDynamics.NonlinearSys.Theorems.AdaptStepFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.AdaptRunFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.CentreAbstrStepFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.CentreAbstrRunFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.LagrangeRemainderFloatOuter
import CORALean.ContDynamics.NonlinearSys.Theorems.MinkowskiDiffAddSubsetReachSet
import CORALean.ContDynamics.NonlinearSys.Theorems.SubMemInputSolution
import CORALean.ContDynamics.NonlinearSys.Theorems.MinkowskiDiffInputSolutionSubsetReachSet
import CORALean.ContDynamics.NonlinearSys.Theorems.ConvexHullTimeIntervalCounterexample
import CORALean.ContDynamics.NonlinearSys.Theorems.ConvexHullTimeIntervalConvexCounterexample
import CORALean.ContDynamics.NonlinearSys.Theorems.CancelRedundantCovers

/-!
# What `NonlinearSys` guarantees

That it generalizes `LinearSys`, in `LinearEmbedding`, and that it reduces to it again:
`LinInputOuter` spends the certificate, `Linearize` turns a confined run linear, `ReachOuter` hands
it on, and `Restrict` makes the one-step forms. `Shift` and `RelinReachOuter` are the loop: a step
is proved on a clock starting at zero, so `Shift` re-anchors the run and `RelinReachOuter` chains
the steps. `RelinTimeIntervalOuter` covers a step's interval; `RelinDeltaReachOuter` spans.

`ConfinedOfBall` and `ConfinementOfSubset` pay off the confinement hypothesis those carry per step:
the run cannot cross a ball of radius `ρ > MΔt` about a step's start, so inflating the computed set
and checking it discharges it, which `ReachUnionOuter` does at run time for `Reach`. The `ReachSet`
files say that of the reachable set rather than of a run. `AbstractionErrorOfHessian` is one
supplier, `AbstrErrLinCenterSubset` minimises what it gives at the centre,
`AbstractionErrorOfLagrange` is the same one order up, and the `PolyAbstractionError` files are the
polynomialization variant's: `OfQuadRemainder` builds one, `GetSubset` splits it, `...OfPoly`
forgets it; `AbstrErrPolySearchEqSome`, `LinReachPolyRegion` and `LinReachPolyOuter` read back what
its search accepted. `GlobalAbstrErrEqLocalAbstrErr` reads a step's error as its local one —
Rådström cancellation — `GlobalAbstrErrLeLocalAbstrErr` reads a run's off its worst step,
`BoxDiameterAbstrSolInf` closes that at a zonotope, `RowNormExpansionOfAnalytic` expands its
coefficients, `GainDimTendstoPow` is the limit gain, `GainDimLePow` its bound, `GainOrderEqTopIff`
the gain order's point; and `AbstrErrLoopFixed`, `SubsetAbstrReach`, `OptDeltatDescent`,
`EstimateGainBracket`, `AdaptStepInvariant`, `SubsetCentreAbstrReach` and `TuneDeltatInitGain` are
what both papers' algorithms are held to. `ReachFloatOuter` is the float run's guarantee.
-/
