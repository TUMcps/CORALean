module

public import CORALean.ContSet.Ellipsoid.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AbsSubLeBoxRadius
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AbsSubLeOfMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AndPointOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.BallContains
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.BoundDotLe
public import CORALean.ContSet.Ellipsoid.Float.Theorems.CartProdOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.CartProdVecExact
public import CORALean.ContSet.Ellipsoid.Float.Theorems.CenterMemConstruct
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.EllipsoidNormLeEllipsoidNormUb
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Enclose2Outer
public import CORALean.ContSet.Ellipsoid.Float.Theorems.EncloseOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.EnclosePointsCovMem
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ExcludesPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ExistsBallOfStrip
public import CORALean.ContSet.Ellipsoid.Float.Theorems.InflateSubPosSemidef
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IntersectStripGollamudiOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IntersectStripLiuOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsBiggerSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsGoodDirSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsOuterFactorSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsPsdSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsequalSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MinkDiffPointOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalCenterEq
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalDominated
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalQEq
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NormUbLe
public import CORALean.ContSet.Ellipsoid.Float.Theorems.OriginExact
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PdCheckSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PlusOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PolygonInner
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ProjectOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.PsdCheckSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.QuadDownLeQuad
public import CORALean.ContSet.Ellipsoid.Float.Theorems.QuadLeQuadUp
public import CORALean.ContSet.Ellipsoid.Float.Theorems.RadiusLe
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ReindexExact
public import CORALean.ContSet.Ellipsoid.Float.Theorems.SymmOfIsSymm
public import CORALean.ContSet.Ellipsoid.Float.Theorems.RepresentsaOriginSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.RepresentsaPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.VerticesOuter
public import CORALean.ContSet.Ellipsoid.Float.Theorems.VolumeLe

/-!
# What a float ellipsoid guarantees, collected

Enclosing under a linear image, where the exact layer is exact, and enclosing
under a Minkowski sum, where it already was. `MemGeneratorError` is what both
pay their rounding through, and `MemNominalSet` is how each reads the nominal
half of a point.
-/
