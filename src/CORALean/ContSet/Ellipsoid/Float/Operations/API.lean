import CORALean.ContSet.Ellipsoid.Float.Operations.GeneratorError
import CORALean.ContSet.Ellipsoid.Float.Operations.MtimesResidual
import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes
import CORALean.ContSet.Ellipsoid.Float.Operations.CenterResidual
import CORALean.ContSet.Ellipsoid.Float.Operations.PlusG
import CORALean.ContSet.Ellipsoid.Float.Operations.PlusGap
import CORALean.ContSet.Ellipsoid.Float.Operations.Plus
import CORALean.ContSet.Ellipsoid.Float.Operations.Project
import CORALean.ContSet.Ellipsoid.Float.Operations.PullbackAbs
import CORALean.ContSet.Ellipsoid.Float.Operations.AbsPullbackLe
import CORALean.ContSet.Ellipsoid.Float.Operations.NominalBoundDot
import CORALean.ContSet.Ellipsoid.Float.Operations.SupportBound
import CORALean.ContSet.Ellipsoid.Float.Operations.Origin
import CORALean.ContSet.Ellipsoid.Float.Operations.Centre
import CORALean.ContSet.Ellipsoid.Float.Operations.Reindex
import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaPoint
import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaOrigin
import CORALean.ContSet.Ellipsoid.Float.Operations.Isequal
import CORALean.ContSet.Ellipsoid.Float.Operations.Vertices
import CORALean.ContSet.Ellipsoid.Float.Operations.NormUb
import CORALean.ContSet.Ellipsoid.Float.Operations.CartProd
import CORALean.ContSet.Ellipsoid.Float.Operations.CartProdVec
import CORALean.ContSet.Ellipsoid.Float.Operations.ContainsPoint
import CORALean.ContSet.Ellipsoid.Float.Operations.MinkDiffPoint
import CORALean.ContSet.Ellipsoid.Float.Operations.Radius
import CORALean.ContSet.Ellipsoid.Float.Operations.IsFullDim
import CORALean.ContSet.Ellipsoid.Float.Operations.Enclose
import CORALean.ContSet.Ellipsoid.Float.Operations.Enclose2
import CORALean.ContSet.Ellipsoid.Float.Operations.IsBigger
import CORALean.ContSet.Ellipsoid.Float.Operations.EllipsoidNormUb
import CORALean.ContSet.Ellipsoid.Float.Operations.Volume
import CORALean.ContSet.Ellipsoid.Float.Operations.Polygon
import CORALean.ContSet.Ellipsoid.Float.Operations.IsGoodDir

/-!
# What a float ellipsoid computes, collected

`mtimes`, which rounds and pays the difference into the box; `supportBound`,
still closed form and still without a linear program, the square root replaced
by a candidate the caller certifies; `plus`, which takes its free parameter as
two scalings rather than one `l`, there being no division either; and
`generatorError`, what all of them charge a rounded generator.
-/
