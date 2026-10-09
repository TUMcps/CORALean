import CORALean.Global.ErrLeNormOfAbsLe
import CORALean.Global.Tensor
import CORALean.Global.Scalar
import CORALean.Global.ExactScalar
import CORALean.Global.NegScalar
import CORALean.Global.Entrywise
import CORALean.Global.Hadamard
import CORALean.Global.Partition
import CORALean.Global.Sort
import CORALean.Global.Block
import CORALean.Global.BlockDiag
import CORALean.Global.AppendProdAdd
import CORALean.Global.AppendLinear
import CORALean.Global.Corners
import CORALean.Global.DropIdx
import CORALean.Global.FoldInduction
import CORALean.Global.CrossProduct
import CORALean.Global.Cost
import CORALean.Global.BoxDiameter
import CORALean.Global.BoxDiameterAddLe
import CORALean.Global.BoxDiameterMulVecImageLe
import CORALean.Global.Err
import CORALean.Global.EuclideanNorm
import CORALean.Global.EuclideanHausdorffDist
import CORALean.Global.EuclideanHausdorffDistAddLe
import CORALean.Global.EuclideanHausdorffDistTriangle
import CORALean.Global.EuclideanHausdorffDistZero
import CORALean.Global.EuclideanGenOpNorm
import CORALean.Global.Radstrom
import CORALean.Global.RadstromEq
import CORALean.Global.RadstromHausdorff
import CORALean.Global.Caratheodory
import CORALean.Global.ConeEdge
import CORALean.Global.EqSmulNCross
import CORALean.Global.Minimax
import CORALean.Global.SuperlinearDecrease
import CORALean.Global.ErrorConvergesToZero
import CORALean.Global.HorizonErrorBudget
import CORALean.Global.HorizonErrorBudgetCounterexample
import CORALean.Global.ConvergenceOrder
import CORALean.Global.LinProg.API
import CORALean.Global.TaylorRemainder
import CORALean.Global.CoordinatePath
import CORALean.Global.MeanValueAE
import CORALean.Global.RobustMeanValueAE
import CORALean.Global.KaucherInner
import CORALean.Global.KaucherInnerCoraCounterexample
import CORALean.Global.KaucherInnerBoxCounterexample
import CORALean.Global.LieDerivative
import CORALean.Global.PreconditionInner
import CORALean.Global.SubmersionFrontier
import CORALean.Global.InnerRangeOfFrontier
import CORALean.Global.InnerTest
import CORALean.Global.InnerRangeTest
import CORALean.Global.InnerRangeTestStepCounterexample
import CORALean.Global.PreconditionedInnerTest
import CORALean.Global.HMatrix
import CORALean.Global.HMatrixRegular
import CORALean.Global.SubmatrixLp
import CORALean.Global.SubmatrixLpCounterexample
import CORALean.Global.LeastSquaresOfNormalEq
import CORALean.Global.PinvLeastSquares
import CORALean.Global.GramTransposeSingular
import CORALean.Global.DmdCandidateLeastSquares
import CORALean.Global.LeastSquaresUniqueLe
import CORALean.Global.ProductInnerRangeCounterexample
import CORALean.Global.CoeffDomination
import CORALean.Global.ElementaryDerivBounds
import CORALean.Global.EvalList
import CORALean.Global.OdeList
import CORALean.Global.SumMulVecImageSubset
import CORALean.Global.CoeffNorm
import CORALean.Global.CubeSubsetHalfspaceIff
import CORALean.Global.L1CircumradiusEqInvInradiusPolar
import CORALean.Global.L1NormLeCardMulNorm
import CORALean.Global.L1NormLeCardMulNormCounterexample
import CORALean.Global.SliceEqSmulConvexHull
import CORALean.Global.ChooseLeExpMulDivPow
import CORALean.Global.CoeffNormBallEq
import CORALean.Global.CoeffNormBallEqCounterexample
import CORALean.Global.EllipsotopeSubsetIff
import CORALean.Global.EllipsotopeSupport
import CORALean.Global.ThetaUniform
import CORALean.Global.ShenmaierBound
import CORALean.Global.ShenmaierHalfspace
import CORALean.Global.ShenmaierHalfspaceNotSubset
import CORALean.Global.ShenmaierHalfspaceProb
import CORALean.Global.ShenmaierHalfspaceCounterexample
import CORALean.Global.ShenmaierVertex
import CORALean.Global.ShenmaierVertexNotSubset
import CORALean.Global.RecList
import CORALean.Global.SqrtDeriv
import CORALean.Global.IteratedDerivArccos
import CORALean.Global.TaylorLagrangeConvex
import CORALean.Global.NearestPointSeparates
import CORALean.Global.PosDefSchurComplement
import CORALean.Global.SumVecMulVecCol
import CORALean.Global.TraceGainLe
import CORALean.Global.TraceMulVecMulVecSelf
import CORALean.Global.VecMulVecMulVecSelf
import CORALean.Global.UltimateBoundOfRecurrence
import CORALean.Global.DmdBlocks
import CORALean.Global.DmdBlocksMulVec
import CORALean.Global.DmdBlocksStack
import CORALean.Global.DmdCandidate
import CORALean.Global.DmdCandidateFit
import CORALean.Global.DmdRegressor
import CORALean.Global.DmdSelect
import CORALean.Global.DmdSelectLe
import CORALean.Global.DmdStack
import CORALean.Global.DmdPinv
import CORALean.Global.DmdReduced
import CORALean.Global.DmdcData
import CORALean.Global.DmdcFit
import CORALean.Global.DmdcReduced
import CORALean.Global.DmdcAlgorithm
import CORALean.Global.DmdcCounterexamples
import CORALean.Global.DmdcExample1
import CORALean.Global.SindyData
import CORALean.Global.SindyThreshold
import CORALean.Global.SindyFixedPoint
import CORALean.Global.DescProd
import CORALean.Global.DescProdState
import CORALean.Global.Jacobian
import CORALean.Global.JacobianMatAffine
import CORALean.Global.JacobianMatParam
import CORALean.Global.LinResidual
import CORALean.Global.StackSelect
import CORALean.Global.StackSelectMulVec
import CORALean.Global.ExistsPosLeOfPosDef
import CORALean.Global.MulVecPosNegBounds
import CORALean.Global.NonnegOfNonnegRecurrence
import CORALean.Global.DoubleSumPosDef
import CORALean.Global.DoubleSumPosDefCounterexample
import CORALean.Global.GeneratorPowerRewrite
import CORALean.Global.InfiniteBusField
import CORALean.Global.InfiniteBusEquilibrium
import CORALean.Global.RobustInvariant
import CORALean.Global.RegionOfAttraction
import CORALean.Global.MemOfReachSubset
import CORALean.Global.SubsetRegionOfAttraction
import CORALean.Global.RegionOfAttractionCounterexample
import CORALean.Global.IpmBall
import CORALean.Global.IpmEllipsoid
import CORALean.Global.IpmBallEq
import CORALean.Global.IpmEllipsoidEq
import CORALean.Global.IpmBallConsistentIff
import CORALean.Global.IpmBallExample

import CORALean.Global.EllipsotopeCentreShift
import CORALean.Global.ExistsGadgetRadii
import CORALean.Global.ZonotopeSubsetEllipsotopeOfLR
import CORALean.Global.ZonotopeSubsetEllipsotopeOfLRCentre
import CORALean.Global.TerminalSetRowConstraints

/-!
# Global definitions, collected

What both arithmetic layers share: the array types, the scalar they compute in,
index partitions, the sort that chooses them, the enumeration of every index but
one, the induction principle carrying a property through a `Fin.foldl`, the
`n`-dimensional cross product that enumeration builds, the entrywise
product bundled as a bilinear map, the corner combinatorics a
box needs, the model every asserted running cost is stated against, the width of
the tightest box over a set and the origin-centred Euclidean radius of that box
(`err`), the Euclidean norm a vector does not carry by default, the Hausdorff
distance read through it, a family of generators' own induced operator norm
(`genOpNorm₂`), the cancellation law that
turns an outer approximation into an inner one, Carathéodory's theorem over a
fixed index, the minimax inequality a parametrized infimum's continuity gives
over two compact sets, when a set-based evaluation shrinks superlinearly, when a
step error converges to zero, a fixed horizon's error budget, the classical
convergence order a point-valued ODE solver either has or does not, the linear
programming every set representation ends up asking for, the dynamic mode decomposition
`identify` is built on (`Dmd…`), power-system identities, regions of attraction, and
interval predictor models (`Ipm…`).

`Float/` is deliberately not collected here — it holds the floating-point
scalar, and importing it would put that in reach of every `Real` file.
-/
