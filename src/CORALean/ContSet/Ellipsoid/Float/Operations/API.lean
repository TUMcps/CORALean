module

public import CORALean.ContSet.Ellipsoid.Float.Operations.AbsorbRounding
public import CORALean.ContSet.Ellipsoid.Float.Operations.AndPoint
public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Operations.BoxRadius
public import CORALean.ContSet.Ellipsoid.Float.Operations.CartProd
public import CORALean.ContSet.Ellipsoid.Float.Operations.CartProdVec
public import CORALean.ContSet.Ellipsoid.Float.Operations.CenterResidual
public import CORALean.ContSet.Ellipsoid.Float.Operations.CholFactor
public import CORALean.ContSet.Ellipsoid.Float.Operations.ContainsPoint
public import CORALean.ContSet.Ellipsoid.Float.Operations.EllipsoidNormUb
public import CORALean.ContSet.Ellipsoid.Float.Operations.Enclose
public import CORALean.ContSet.Ellipsoid.Float.Operations.EnclosePointsCov
public import CORALean.ContSet.Ellipsoid.Float.Operations.ExcludesPoint
public import CORALean.ContSet.Ellipsoid.Float.Operations.Inflate
public import CORALean.ContSet.Ellipsoid.Float.Operations.IntersectStripGollamudi
public import CORALean.ContSet.Ellipsoid.Float.Operations.IntersectStripLiu
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsBigger
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsFullDim
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsGoodDir
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsOuterFactor
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsPsd
public import CORALean.ContSet.Ellipsoid.Float.Operations.Isequal
public import CORALean.ContSet.Ellipsoid.Float.Operations.Materialise
public import CORALean.ContSet.Ellipsoid.Float.Operations.MinkDiffPoint
public import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes
public import CORALean.ContSet.Ellipsoid.Float.Operations.MtimesResidual
public import CORALean.ContSet.Ellipsoid.Float.Operations.NominalBoundDot
public import CORALean.ContSet.Ellipsoid.Float.Operations.NormUb
public import CORALean.ContSet.Ellipsoid.Float.Operations.OfPoint
public import CORALean.ContSet.Ellipsoid.Float.Operations.Origin
public import CORALean.ContSet.Ellipsoid.Float.Operations.OuterFactor
public import CORALean.ContSet.Ellipsoid.Float.Operations.PdCheck
public import CORALean.ContSet.Ellipsoid.Float.Operations.Plus
public import CORALean.ContSet.Ellipsoid.Float.Operations.Polygon
public import CORALean.ContSet.Ellipsoid.Float.Operations.Project
public import CORALean.ContSet.Ellipsoid.Float.Operations.PsdCheck
public import CORALean.ContSet.Ellipsoid.Float.Operations.Radius
public import CORALean.ContSet.Ellipsoid.Float.Operations.Reindex
public import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaOrigin
public import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Ellipsoid.Float.Operations.SupportBound
public import CORALean.ContSet.Ellipsoid.Float.Operations.Vertices
public import CORALean.ContSet.Ellipsoid.Float.Operations.Volume

/-!
# What a float ellipsoid computes, collected

`mtimes`, which rounds and pays the difference into the box; `supportBound`,
still closed form and still without a linear program, the square root replaced
by a candidate the caller certifies; `plus`, which takes its free parameter as
two scalings rather than one `l`, there being no division either; and
`generatorError`, what all of them charge a rounded generator.
-/
