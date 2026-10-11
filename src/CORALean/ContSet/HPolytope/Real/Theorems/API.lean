import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact
import CORALean.ContSet.HPolytope.Real.Theorems.Convex
import CORALean.ContSet.HPolytope.Real.Theorems.ExistsConstructEqImageFst
import CORALean.ContSet.HPolytope.Real.Theorems.ExtremePoints
import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
import CORALean.ContSet.HPolytope.Real.Theorems.LinCombOfOuter
import CORALean.ContSet.HPolytope.Real.Theorems.MapEquivExact
import CORALean.ContSet.HPolytope.Real.Theorems.MemConstruct
import CORALean.ContSet.HPolytope.Real.Theorems.MemIntersection
import CORALean.ContSet.HPolytope.Real.Theorems.MinkDiffOfInner
import CORALean.ContSet.HPolytope.Real.Theorems.MinusExact
import CORALean.ContSet.HPolytope.Real.Theorems.MtimesOfOuter
import CORALean.ContSet.HPolytope.Real.Theorems.OfPointMem
import CORALean.ContSet.HPolytope.Real.Theorems.OfPointMemIff
import CORALean.ContSet.HPolytope.Real.Theorems.PlusOfOuter
import CORALean.ContSet.HPolytope.Real.Theorems.StackExact
import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact
import CORALean.ContSet.HPolytope.Real.Theorems.LiftExact
import CORALean.ContSet.HPolytope.Real.Theorems.MldivideCoraCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.NormalizeConstraintsExact
import CORALean.ContSet.HPolytope.Real.Theorems.NormalizeRowsExact
import CORALean.ContSet.HPolytope.Real.Theorems.ProjectHighDimExact
import CORALean.ContSet.HPolytope.Real.Theorems.MemIneqsOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsSubsetIff
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsSubsetIffCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetOfExistsCert
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetIffOfInjective
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeCertNecessary
import CORALean.ContSet.HPolytope.Real.Theorems.SumAHPolytopeSubsetIneqsIff
import CORALean.ContSet.HPolytope.Real.Theorems.SumAHPolytopeSubsetIneqsIffCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetSumOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.EqZeroOfMulVecNonpos
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetConvexHullOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetConvexHullOfCertCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetConvexHullAHOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetConvexHullAHOfCertCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.ExistsSubsetIffDisjunctiveCert
import CORALean.ContSet.HPolytope.Real.Theorems.ExistsSubsetIffDisjunctiveCertCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetAddBallOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.HausdorffDistLeOfSubsetAddBall
import CORALean.ContSet.HPolytope.Real.Theorems.ProjectionInnerOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.ProjectionInnerOfCertCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeEqOfLeftInverse
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeEqOfLeftInverseCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeImageAffine
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeAddEq
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeInterEq
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeInterEqCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.PolyNormLeIff
import CORALean.ContSet.HPolytope.Real.Theorems.PolyNormIsAsymmNorm
import CORALean.ContSet.HPolytope.Real.Theorems.PolyNormIsAsymmNormCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.IsGreatestPolyNormEllipsotope
import CORALean.ContSet.HPolytope.Real.Theorems.IsGreatestPolyNormEllipsotopeCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.ReduceOverDomainRows
import CORALean.ContSet.HPolytope.Real.Theorems.ReduceOverDomainOuter
import CORALean.ContSet.HPolytope.Real.Theorems.ReduceOverDomainInner
import CORALean.ContSet.HPolytope.Real.Theorems.AffineHullBasisSpec
import CORALean.ContSet.HPolytope.Real.Theorems.ChebyshevNotUnique
import CORALean.ContSet.HPolytope.Real.Theorems.ExistsPosStepStrict
import CORALean.ContSet.HPolytope.Real.Theorems.GenerateRandomHBoundedFullDim
import CORALean.ContSet.HPolytope.Real.Theorems.ImageIneqsOfFactor
import CORALean.ContSet.HPolytope.Real.Theorems.ImageIneqsOfInvertible
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsAddEqProjection
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsBlockDiagEq
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsDegenerateChebyshevCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsEqDropIffSupportFunc
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsEqEmptyIff
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsEqIffSupportFunc
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsEqImageRestrict
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsEqOfStrict
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsEqOfStrictCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsInterNonemptyIff
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsSubsetIffSupportFunc
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsUnitRowsMinimal
import CORALean.ContSet.HPolytope.Real.Theorems.InteriorNonemptyIffChebyshev
import CORALean.ContSet.HPolytope.Real.Theorems.InteriorRestrictNonempty
import CORALean.ContSet.HPolytope.Real.Theorems.IsBoundedIffSimplexSupportFunc
import CORALean.ContSet.HPolytope.Real.Theorems.IsFullDimCoraCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.IsequalNondegDuplicateCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.IsequalNondegIff
import CORALean.ContSet.HPolytope.Real.Theorems.IsequalNondegPrintedCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.IsGreatestSignedUnit
import CORALean.ContSet.HPolytope.Real.Theorems.MinkowskiDiffIneqsEq
import CORALean.ContSet.HPolytope.Real.Theorems.SimplexRowsRedundantCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.SuccLeOfIsBounded
import CORALean.ContSet.HPolytope.Real.Theorems.TightRedundantCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.IsGreatestBallRadius
import CORALean.ContSet.HPolytope.Real.Theorems.RestrictConstruct
import CORALean.ContSet.HPolytope.Real.Theorems.CompactZerosExact
import CORALean.ContSet.HPolytope.Real.Theorems.CompactAlignedIneqExact
import CORALean.ContSet.HPolytope.Real.Theorems.MoveToEqConstruct
import CORALean.ContSet.HPolytope.Real.Theorems.AtoAeStateSpec
import CORALean.ContSet.HPolytope.Real.Theorems.CompactAtoAeExact
import CORALean.ContSet.HPolytope.Real.Theorems.RepresentsaFullspaceIff
import CORALean.ContSet.HPolytope.Real.Theorems.IsLPCentreMem
import CORALean.ContSet.HPolytope.Real.Theorems.VolumeInterval
import CORALean.ContSet.HPolytope.Real.Theorems.MemIffRows
import CORALean.ContSet.HPolytope.Real.Theorems.VolumeLtTop
import CORALean.ContSet.HPolytope.Real.Theorems.ExistsConstructEqImageAffine
import CORALean.ContSet.HPolytope.Real.Theorems.BallSubsetIneqsIff
import CORALean.ContSet.HPolytope.Real.Theorems.EmptyRedundantCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.EmptySetRowsMinimal
import CORALean.ContSet.HPolytope.Real.Theorems.NaiveHalfspaceNotSubset
import CORALean.ContSet.HPolytope.Real.Theorems.NaiveHalfspacePrintedCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.NaiveHalfspaceValueLe
import CORALean.ContSet.HPolytope.Real.Theorems.NaiveHalfspaceAccuracyCounterexample
import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetIneqsIff

/-!
# What `HPolytope` guarantees

The operations whose rows the inputs determine, exactly; the rest enclosing,
each in one line off `subset_ofBounds`. Convex and closed, but not bounded:
unbounded is what this representation admits and a vertex one cannot.
`MemConstruct` names the pair of constraint blocks every one of them is stated
against. `MinkDiffOfInner` is the one guarantee running the other way: an inner
approximation of the Minkowski difference, needing `hker` on the equality rows.
`OfPointMem` is the one at `Vec ℝ n` alone, `LinearMap.proj` needing coordinates.
-/
