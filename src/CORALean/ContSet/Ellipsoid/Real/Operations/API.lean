module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
public import CORALean.ContSet.Ellipsoid.Real.Operations.CartProd
public import CORALean.ContSet.Ellipsoid.Real.Operations.CartProdVec
public import CORALean.ContSet.Ellipsoid.Real.Operations.Rank
public import CORALean.ContSet.Ellipsoid.Real.Operations.Map
public import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
public import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
public import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec
public import CORALean.ContSet.Ellipsoid.Real.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Real.Operations.SupportBound
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfPoint
public import CORALean.ContSet.Ellipsoid.Real.Operations.Project
public import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Ellipsoid.Real.Operations.Isequal
public import CORALean.ContSet.Ellipsoid.Real.Operations.ConvHullCora
public import CORALean.ContSet.Ellipsoid.Real.Operations.ContainsEllipsoidCora
public import CORALean.ContSet.Ellipsoid.Real.Operations.Vertices
public import CORALean.ContSet.Ellipsoid.Real.Operations.NormUb
public import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
public import CORALean.ContSet.Ellipsoid.Real.Operations.EllipsoidNorm
public import CORALean.ContSet.Ellipsoid.Real.Operations.Radius
public import CORALean.ContSet.Ellipsoid.Real.Operations.IsBigger
public import CORALean.ContSet.Ellipsoid.Real.Operations.IsBiggerCora
public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripGollamudi1D
public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripGollamudi
public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripLiu1D
public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripLiu
public import CORALean.ContSet.Ellipsoid.Real.Operations.Enclose
public import CORALean.ContSet.Ellipsoid.Real.Operations.MinkDiffPoint
public import CORALean.ContSet.Ellipsoid.Real.Operations.ContainsPoint
public import CORALean.ContSet.Ellipsoid.Real.Operations.IsOrOuter
public import CORALean.ContSet.Ellipsoid.Real.Operations.Enclose2
public import CORALean.ContSet.Ellipsoid.Real.Operations.NormExact
public import CORALean.ContSet.Ellipsoid.Real.Operations.Generators
public import CORALean.ContSet.Ellipsoid.Real.Operations.AndPoint
public import CORALean.ContSet.Ellipsoid.Real.Operations.EnclosePointsOriented
public import CORALean.ContSet.Ellipsoid.Real.Operations.EnclosePointsNt
public import CORALean.ContSet.Ellipsoid.Real.Operations.EnclosePointsMaxDist
public import CORALean.ContSet.Ellipsoid.Real.Operations.EnclosePointsCov
public import CORALean.ContSet.Ellipsoid.Real.Operations.IsIntersectingPoint
public import CORALean.ContSet.Ellipsoid.Real.Operations.CutPrecision
public import CORALean.ContSet.Ellipsoid.Real.Operations.CutShape
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderElemSymm
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderInvSum
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderLamSum
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderLogDet
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderMu
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStep
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfShape
public import CORALean.ContSet.Ellipsoid.Real.Operations.Polygon
public import CORALean.ContSet.Ellipsoid.Real.Operations.IsBadDir
public import CORALean.ContSet.Ellipsoid.Real.Operations.Goffin
public import CORALean.ContSet.Ellipsoid.Real.Operations.GoffinCut
public import CORALean.ContSet.Ellipsoid.Real.Operations.RepresentsaHyperplaneCora

/-!
# What an ellipsoid computes, collected

`mtimes` and the `map` it is, exact and the reason the generator form is stored;
`supportBound`, closed form in every direction; and `plus`, which encloses and
takes the parameter that enclosure needs. `Shape` is CORA's `Q`, read back off
the generators so the correspondence can be checked. `ofPoint` is the
degenerate case, `G` with no columns.
-/
