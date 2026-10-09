import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.QMemConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqImage
import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsBounded
import CORALean.ContSet.Ellipsoid.Real.Theorems.ContinuousAffine
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsClosed
import CORALean.ContSet.Ellipsoid.Real.Theorems.MapExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusOuter
import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusScalingsAdmissible
import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestSupport
import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMem
import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Ellipsoid.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.ProjectExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.RepresentsaPointIff
import CORALean.ContSet.Ellipsoid.Real.Theorems.RepresentsaOriginIff
import CORALean.ContSet.Ellipsoid.Real.Theorems.RankShape
import CORALean.ContSet.Ellipsoid.Real.Theorems.CartProdOuter
import CORALean.ContSet.Ellipsoid.Real.Theorems.CartProdVecExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsFullDimIff
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsequalConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.VerticesExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.NormUbLe
import CORALean.ContSet.Ellipsoid.Real.Theorems.VolumeEqSquare
import CORALean.ContSet.Ellipsoid.Real.Theorems.VolumeEqZero
import CORALean.ContSet.Ellipsoid.Real.Theorems.EllipsoidNormLeOneIff
import CORALean.ContSet.Ellipsoid.Real.Theorems.ShapeMtimes
import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportFuncEq
import CORALean.ContSet.Ellipsoid.Real.Theorems.AffineImageExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.MinkowskiDiffNonemptyIff
import CORALean.ContSet.Ellipsoid.Real.Theorems.InterHyperplaneEq
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestDot
import CORALean.ContSet.Ellipsoid.Real.Theorems.DistPointEqMax
import CORALean.ContSet.Ellipsoid.Real.Theorems.DistPointNonnegCounterexample
import CORALean.ContSet.Ellipsoid.Real.Theorems.DistEllipsoidEqMax
import CORALean.ContSet.Ellipsoid.Real.Theorems.DistHyperplaneEq
import CORALean.ContSet.Ellipsoid.Real.Theorems.DotTranspose
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsUnitShape
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestRadius
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsBiggerIffSubset
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsBiggerCoraCounterexample
import CORALean.ContSet.Ellipsoid.Real.Theorems.IntersectStripGollamudi1DCounterexample
import CORALean.ContSet.Ellipsoid.Real.Theorems.EncloseOuter
import CORALean.ContSet.Ellipsoid.Real.Theorems.EncloseCoraCounterexample
import CORALean.ContSet.Ellipsoid.Real.Theorems.MinkDiffPointExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.ContainsPointIff
import CORALean.ContSet.Ellipsoid.Real.Theorems.SegmentsSubsetOfIsOrOuter
import CORALean.ContSet.Ellipsoid.Real.Theorems.Enclose2Outer
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestNorm
import CORALean.ContSet.Ellipsoid.Real.Theorems.GeneratorsMulTranspose
import CORALean.ContSet.Ellipsoid.Real.Theorems.AndPointExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.EnclosePointsCovMem
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsIntersectingPointIff

/-!
# What an ellipsoid guarantees, collected

Exact under a linear image; enclosing under a Minkowski sum, and only ever
enclosing there — at every admissible pair of scalings, of which
`PlusScalingsAdmissible` picks out the curve Kurzhanski and Varaiya's `l`
sweeps. `SupportBoundAttained` is what says the certificates give nothing away,
and convexity, compactness and boundedness are what the reachability theorems
consume. `ConstructEqImage` is what all three of those last transfer from the
unit ball through. `mem_ofPoint` reuses `mem_construct` at the empty
coefficient vector.
-/
