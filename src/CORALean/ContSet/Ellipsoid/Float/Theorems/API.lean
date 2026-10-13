module

public import CORALean.ContSet.Ellipsoid.Float.Theorems.BoundDotLe
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesK
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PlusK
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PlusOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ProjectOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Convex
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsCompact
public import CORALean.ContSet.Ellipsoid.Float.Theorems.OriginExact
public import CORALean.ContSet.Ellipsoid.Float.Theorems.CentreMemConstruct
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ReindexExact
public import CORALean.ContSet.Ellipsoid.Float.Theorems.RepresentsaPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.RepresentsaOriginSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsequalSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.VerticesOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NormUbLe
public import CORALean.ContSet.Ellipsoid.Float.Theorems.CartProdOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.CartProdVecExact
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MinkDiffPointOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.RadiusLe
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.EncloseOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Enclose2Outer
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsBiggerSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.EllipsoidNormLeEllipsoidNormUb
public import CORALean.ContSet.Ellipsoid.Float.Theorems.VolumeLe
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PolygonInner
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsGoodDirSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.OfPointExact
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ExcludesPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AndPointOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.EnclosePointsCovMem
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ExistsBallOfStrip
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IntersectStripGollamudiOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IntersectStripLiuOuter

/-!
# What a float ellipsoid guarantees, collected

Enclosing under a linear image, where the exact layer is exact, and enclosing
under a Minkowski sum, where it already was. `MemGeneratorError` is what both
pay their rounding through, and `MemNominalSet` is how each reads the nominal
half of a point.
-/
