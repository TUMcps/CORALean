import CORALean.ContSet.Interval.Real.Theorems.BoundaryRatioIsGreatest
import CORALean.ContSet.Interval.Real.Theorems.DivMemCornerHull
import CORALean.ContSet.Interval.Real.Theorems.ArgEqArctanOfRePos
import CORALean.ContSet.Interval.Real.Theorems.ArgEqPiDivTwoSubArctanOfImPos
import CORALean.ContSet.Interval.Real.Theorems.ArgEqNegPiDivTwoSubArctanOfImNeg
import CORALean.ContSet.Interval.Real.Theorems.Atan2EnclosureOfPosInfX
import CORALean.ContSet.Interval.Real.Theorems.Atan2EnclosureOfPosInfY
import CORALean.ContSet.Interval.Real.Theorems.Atan2EnclosureOfNegSupY
import CORALean.ContSet.Interval.Real.Theorems.AbsMulLoMulHiLe
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.Interval.Real.Theorems.IsBounded
import CORALean.ContSet.Interval.Real.Theorems.IsClosed
import CORALean.ContSet.Interval.Real.Theorems.IsCompact
import CORALean.ContSet.Interval.Real.Theorems.IsNonempty
import CORALean.ContSet.Interval.Real.Theorems.NotIsNonempty
import CORALean.ContSet.Interval.Real.Theorems.AbsSubCenterLe
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.PlusExact
import CORALean.ContSet.Interval.Real.Theorems.MinkDiffInner
import CORALean.ContSet.Interval.Real.Theorems.MinkDiffExact
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints
import CORALean.ContSet.Interval.Real.Theorems.DivBetweenEndpoints
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
import CORALean.ContSet.Interval.Real.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Real.Theorems.MemCenter
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.ContSet.Interval.Real.Theorems.RecentreZeroMem
import CORALean.ContSet.Interval.Real.Theorems.RecentreSubMem
import CORALean.ContSet.Interval.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Real.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Real.Theorems.MatMulSymmPoint
import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter
import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
import CORALean.ContSet.Interval.Real.Theorems.MtimesIsNonempty
import CORALean.ContSet.Interval.Real.Theorems.SupportBoundEntrywiseAttained
import CORALean.ContSet.Interval.Real.Theorems.SupportBoundAttained
import CORALean.ContSet.Interval.Real.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Real.Theorems.MtimesWidth
import CORALean.ContSet.Interval.Real.Theorems.ReindexExact
import CORALean.ContSet.Interval.Real.Theorems.SplitAtCover
import CORALean.ContSet.Interval.Real.Theorems.HausdorffDist2AddLeBoxRadius
import CORALean.ContSet.Interval.Real.Theorems.UminusExact
import CORALean.ContSet.Interval.Real.Theorems.UplusExact
import CORALean.ContSet.Interval.Real.Theorems.MinusEqPlusUminus
import CORALean.ContSet.Interval.Real.Theorems.MinusOuter
import CORALean.ContSet.Interval.Real.Theorems.MinusExact
import CORALean.ContSet.Interval.Real.Theorems.InfimumMemConstruct
import CORALean.ContSet.Interval.Real.Theorems.SupremumMemConstruct
import CORALean.ContSet.Interval.Real.Theorems.OrOuter
import CORALean.ContSet.Interval.Real.Theorems.ConvHullOuter
import CORALean.ContSet.Interval.Real.Theorems.EnclosePointsOuter
import CORALean.ContSet.Interval.Real.Theorems.OriginExact
import CORALean.ContSet.Interval.Real.Theorems.AbsExact
import CORALean.ContSet.Interval.Real.Theorems.ConstructEqSingleton
import CORALean.ContSet.Interval.Real.Theorems.EmptyExact
import CORALean.ContSet.Interval.Real.Theorems.ExistsMulEq
import CORALean.ContSet.Interval.Real.Theorems.ExpExact
import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact
import CORALean.ContSet.Interval.Real.Theorems.AntitoneImageExact
import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageOuter
import CORALean.ContSet.Interval.Real.Theorems.SqrtExact
import CORALean.ContSet.Interval.Real.Theorems.LogExact
import CORALean.ContSet.Interval.Real.Theorems.AtanExact
import CORALean.ContSet.Interval.Real.Theorems.SinhExact
import CORALean.ContSet.Interval.Real.Theorems.AsinhExact
import CORALean.ContSet.Interval.Real.Theorems.TanhExact
import CORALean.ContSet.Interval.Real.Theorems.AsinExact
import CORALean.ContSet.Interval.Real.Theorems.AcosExact
import CORALean.ContSet.Interval.Real.Theorems.SignMonotone
import CORALean.ContSet.Interval.Real.Theorems.SignOuter
import CORALean.ContSet.Interval.Real.Theorems.RoundOuter
import CORALean.ContSet.Interval.Real.Theorems.LeIffSubset
import CORALean.ContSet.Interval.Real.Theorems.LeSubset
import CORALean.ContSet.Interval.Real.Theorems.LtSubset
import CORALean.ContSet.Interval.Real.Theorems.ProjectExact
import CORALean.ContSet.Interval.Real.Theorems.ProjectHighDimExact
import CORALean.ContSet.Interval.Real.Theorems.ProjectOuter
import CORALean.ContSet.Interval.Real.Theorems.RepresentsaEmptySetIff
import CORALean.ContSet.Interval.Real.Theorems.RepresentsaOriginIff
import CORALean.ContSet.Interval.Real.Theorems.RepresentsaPointIff
import CORALean.ContSet.Interval.Real.Theorems.SingletonOfInfEqSup
import CORALean.ContSet.Interval.Real.Theorems.TimesExact
import CORALean.ContSet.Interval.Real.Theorems.TimesOuter
import CORALean.ContSet.Interval.Real.Theorems.VolumeEq
import CORALean.ContSet.Interval.Real.Theorems.IsFullDimIff
import CORALean.ContSet.Interval.Real.Theorems.NormLe
import CORALean.ContSet.Interval.Real.Theorems.NormAttained
import CORALean.ContSet.Interval.Real.Theorems.MaxExact
import CORALean.ContSet.Interval.Real.Theorems.MinExact
import CORALean.ContSet.Interval.Real.Theorems.MinEqUminusMax
import CORALean.ContSet.Interval.Real.Theorems.EnlargeExact
import CORALean.ContSet.Interval.Real.Theorems.CenterSubRadius
import CORALean.ContSet.Interval.Real.Theorems.CenterAddRadius
import CORALean.ContSet.Interval.Real.Theorems.MemOfCenterRadius
import CORALean.ContSet.Interval.Real.Theorems.IntervalMatrixEq
import CORALean.ContSet.Interval.Real.Theorems.NormSubCenterLe
import CORALean.ContSet.Interval.Real.Theorems.SupSubCenter
import CORALean.ContSet.Interval.Real.Theorems.Radius2IsLeast
import CORALean.ContSet.Interval.Real.Theorems.IsequalConstructEq
import CORALean.ContSet.Interval.Real.Theorems.IsequalIff
import CORALean.ContSet.Interval.Real.Theorems.TransposeExact
import CORALean.ContSet.Interval.Real.Theorems.CtransposeExact
import CORALean.ContSet.Interval.Real.Theorems.Sum1Exact
import CORALean.ContSet.Interval.Real.Theorems.Sum2Exact
import CORALean.ContSet.Interval.Real.Theorems.AcoshExact
import CORALean.ContSet.Interval.Real.Theorems.AtanhExact
import CORALean.ContSet.Interval.Real.Theorems.TanExact
import CORALean.ContSet.Interval.Real.Theorems.MaskExact
import CORALean.ContSet.Interval.Real.Theorems.TrilExact
import CORALean.ContSet.Interval.Real.Theorems.TriuExact
import CORALean.ContSet.Interval.Real.Theorems.HorzcatExact
import CORALean.ContSet.Interval.Real.Theorems.VertcatExact
import CORALean.ContSet.Interval.Real.Theorems.PartitionExact
import CORALean.ContSet.Interval.Real.Theorems.DiagExact
import CORALean.ContSet.Interval.Real.Theorems.DiagVecExact
import CORALean.ContSet.Interval.Real.Theorems.QuadMapOuter
import CORALean.ContSet.Interval.Real.Theorems.QuadMapMixedOuter
import CORALean.ContSet.Interval.Real.Theorems.CoshExact
import CORALean.ContSet.Interval.Real.Theorems.ImageCosIcc
import CORALean.ContSet.Interval.Real.Theorems.CosExact
import CORALean.ContSet.Interval.Real.Theorems.SinExact
import CORALean.ContSet.Interval.Real.Theorems.Prod1Exact
import CORALean.ContSet.Interval.Real.Theorems.KronOuter
import CORALean.ContSet.Interval.Real.Theorems.RecipExact
import CORALean.ContSet.Interval.Real.Theorems.RdivideExact
import CORALean.ContSet.Interval.Real.Theorems.MrdivideExact
import CORALean.ContSet.Interval.Real.Theorems.InvBetween
import CORALean.ContSet.Interval.Real.Theorems.MatPowSmul
import CORALean.ContSet.Interval.Real.Theorems.AbsMaxSmul
import CORALean.ContSet.Interval.Real.Theorems.ExistsMeasurableMulVecEq
import CORALean.ContSet.Interval.Real.Theorems.ExistsNormEqAbsMax
import CORALean.ContSet.Interval.Real.Theorems.PowerBetween
import CORALean.ContSet.Interval.Real.Theorems.PowerExact
import CORALean.ContSet.Interval.Real.Theorems.Atan2CoraCounterexample
import CORALean.ContSet.Interval.Real.Theorems.MulMatEntryImage
import CORALean.ContSet.Interval.Real.Theorems.ConstructSubsetConvexHullVertices
import CORALean.ContSet.Interval.Real.Theorems.InfExact
import CORALean.ContSet.Interval.Real.Theorems.LiftExact
import CORALean.ContSet.Interval.Real.Theorems.DiracOuter
import CORALean.ContSet.Interval.Real.Theorems.DiracOffZero
import CORALean.ContSet.Interval.Real.Theorems.StlIntervalExact
import CORALean.ContSet.Interval.Real.Theorems.DiracZeroMem
import CORALean.ContSet.Interval.Real.Theorems.ModSubModCases
import CORALean.ContSet.Interval.Real.Theorems.SinByRegionsExact
import CORALean.ContSet.Interval.Real.Theorems.CosByRegionsExact
import CORALean.ContSet.Interval.Real.Theorems.TanUnboundedOfPole
import CORALean.ContSet.Interval.Real.Theorems.TanByRegionsExact
import CORALean.ContSet.Interval.Real.Theorems.CotByRegionsExact
import CORALean.ContSet.Interval.Real.Theorems.InvImageIccCases
import CORALean.ContSet.Interval.Real.Theorems.HullIsLeast
import CORALean.ContSet.Interval.Real.Theorems.HullAdd
import CORALean.ContSet.Interval.Real.Theorems.HullImageOfNonneg
import CORALean.ContSet.Interval.Real.Theorems.ImageOfNonnegCounterexample
import CORALean.ContSet.Interval.Real.Theorems.ExtremalLoIsLeast
import CORALean.ContSet.Interval.Real.Theorems.ExtremalHiIsGreatest
import CORALean.ContSet.Interval.Real.Theorems.ZeroMemExtremal
import CORALean.ContSet.Interval.Real.Theorems.PolyBoxReviseLeftLe
import CORALean.ContSet.Interval.Real.Theorems.PolyBoxReviseRightGe
import CORALean.ContSet.Interval.Real.Theorems.PolyBoxReviseIsContractor
import CORALean.ContSet.Interval.Real.Theorems.ExistsZeroIffExtrema
import CORALean.ContSet.Interval.Real.Theorems.ExistsZeroIffExtremaCounterexample
import CORALean.ContSet.Interval.Real.Theorems.NaturalExtensionDependency
import CORALean.ContSet.Interval.Real.Theorems.ExtremalExample
import CORALean.ContSet.Interval.Real.Theorems.PolyBoxRewriteRemarks
import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsInterHyperplaneIff
import CORALean.ContSet.Interval.Real.Theorems.ExploreBNStepSpec
import CORALean.ContSet.Interval.Real.Theorems.ExploreBNVisitsSumLe
import CORALean.ContSet.Interval.Real.Theorems.MemExploreBNVisits
import CORALean.ContSet.Interval.Real.Theorems.ExploreBNEqExtremePoints
import CORALean.ContSet.Interval.Real.Theorems.CornerSumAddLe
import CORALean.ContSet.Interval.Real.Theorems.CornerSumUpdate
import CORALean.ContSet.Interval.Real.Theorems.CornerSumMono
import CORALean.ContSet.Interval.Real.Theorems.EdgeMemHyperplaneIff
import CORALean.ContSet.Interval.Real.Theorems.CardPrefixFace
import CORALean.ContSet.Interval.Real.Theorems.ExistsUniqueBorderVertex
import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsComplementIff
import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsTranslateIff
import CORALean.ContSet.Interval.Real.Theorems.MemExtremePointsScaleIff
import CORALean.ContSet.Interval.Real.Theorems.ScaleBoxCounterexample
import CORALean.ContSet.Interval.Real.Theorems.ExploreBNNegCounterexample
import CORALean.ContSet.Interval.Real.Theorems.ExploreBNUnorderedCounterexample
import CORALean.ContSet.Interval.Real.Theorems.ExploreBNSort
import CORALean.ContSet.Interval.Real.Theorems.VertexEdgeSolutionIff
import CORALean.ContSet.Interval.Real.Theorems.VertexEdgeSolutionCounterexample
import CORALean.ContSet.Interval.Real.Theorems.ExtremePointsFaceEq5
import CORALean.ContSet.Interval.Real.Theorems.FaceInterHyperplaneNonempty
import CORALean.ContSet.Interval.Real.Theorems.PrefixFacePartition
import CORALean.ContSet.Interval.Real.Theorems.PieceHasBorderVertex
import CORALean.ContSet.Interval.Real.Theorems.PieceSolutionCounterexample
import CORALean.ContSet.Interval.Real.Theorems.BoxPlaneIntersectNaiveEq
import CORALean.ContSet.Interval.Real.Theorems.ExploreBNVisitsLengthLeCard

/-!
# What `Interval` guarantees

An enclosure per operation — `plus` exactly so, `minkDiff` exactly so and inner,
unconditionally — and the topological facts a set-valued integral needs:
convex, closed, bounded, and the two last combined into the compactness an
interface field asks for. `MemMat` is membership at an interval matrix, read by
row and column, and `MemCenter` is the one point a box always offers a layer
that has to commit to a value. `RecentreZeroMem`/`RecentreSubMem` need that
same nonemptiness to place the origin, a crossed box denoting `∅` instead.
`MtimesIsNonempty`/`MtimesWidth`: an image box is non-empty, and how wide it is.
`DivBetweenEndpoints` solves `MulBetweenEndpoints` back for the point. `MulBetweenCorners` is
the scalar fact `mtimes*` products against an interval matrix share, and `MatMulOuter` is its
use on `matMul`, an enclosure since a product's `k`-summands bound independently.
`MatMulSymmPoint` is the case that loses nothing: a symmetric left factor
against a point right one collapses to `|M|` scaled by the radius. `MatPowOuter`
lifts the general bound along `matPow`'s recursion, growing the same dependency
loss with every power. `SmulOuter` is `MulBetweenEndpoints` read back through
`Entrywise`. `SplitAtCover` is why `splitAt` is sound to feed
`NeuralNetwork.holds_of_split`: its two halves cover the box they bisected.
`NormLeAbsMax` bounds the `l∞` operator norm uniformly over a box by its
`AbsMax`, attained (`ExistsNormEqAbsMax`); `MatPowSmul`/`AbsMaxSmul` scale both, and
`ExistsMeasurableMulVecEq` picks a member measurably. `HausdorffDist2AddLeBoxRadius` bounds
a Minkowski sum's move by a box holding the summand.
-/
