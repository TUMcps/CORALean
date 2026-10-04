import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
import CORALean.ContSet.Ellipsoid.Real.Operations.CartProd
import CORALean.ContSet.Ellipsoid.Real.Operations.CartProdVec
import CORALean.ContSet.Ellipsoid.Real.Operations.Rank
import CORALean.ContSet.Ellipsoid.Real.Operations.Map
import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec
import CORALean.ContSet.Ellipsoid.Real.Operations.ApplyEqDotProduct
import CORALean.ContSet.Ellipsoid.Real.Operations.Pullback
import CORALean.ContSet.Ellipsoid.Real.Operations.ApplyMulVec
import CORALean.ContSet.Ellipsoid.Real.Operations.SupportBound
import CORALean.ContSet.Ellipsoid.Real.Operations.OfPoint
import CORALean.ContSet.Ellipsoid.Real.Operations.Project
import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaPoint
import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.Ellipsoid.Real.Operations.Isequal
import CORALean.ContSet.Ellipsoid.Real.Operations.Vertices
import CORALean.ContSet.Ellipsoid.Real.Operations.NormUb
import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
import CORALean.ContSet.Ellipsoid.Real.Operations.EllipsoidNorm
import CORALean.ContSet.Ellipsoid.Real.Operations.Radius
import CORALean.ContSet.Ellipsoid.Real.Operations.IsBigger
import CORALean.ContSet.Ellipsoid.Real.Operations.IsBiggerCora
import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripGollamudi1D
import CORALean.ContSet.Ellipsoid.Real.Operations.Enclose
import CORALean.ContSet.Ellipsoid.Real.Operations.MinkDiffPoint
import CORALean.ContSet.Ellipsoid.Real.Operations.ContainsPoint
import CORALean.ContSet.Ellipsoid.Real.Operations.IsOrOuter
import CORALean.ContSet.Ellipsoid.Real.Operations.Enclose2

/-!
# What an ellipsoid computes, collected

`mtimes` and the `map` it is, exact and the reason the generator form is stored;
`supportBound`, closed form in every direction; and `plus`, which encloses and
takes the parameter that enclosure needs. `Shape` is CORA's `Q`, read back off
the generators so the correspondence can be checked. `ofPoint` is the
degenerate case, `G` with no columns.
-/
