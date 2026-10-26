module

public import CORALean.ContSet.SpectraShadow.Float.Operations.GenerateESumRep
public import CORALean.ContSet.SpectraShadow.Float.Operations.CenterResidual
public import CORALean.ContSet.SpectraShadow.Float.Operations.CartProd
public import CORALean.ContSet.SpectraShadow.Float.Operations.Empty
public import CORALean.ContSet.SpectraShadow.Float.Operations.Inf
public import CORALean.ContSet.SpectraShadow.Float.Operations.Mtimes
public import CORALean.ContSet.SpectraShadow.Float.Operations.PadLeft
public import CORALean.ContSet.SpectraShadow.Float.Operations.PadRight
public import CORALean.ContSet.SpectraShadow.Float.Operations.Plus
public import CORALean.ContSet.SpectraShadow.Float.Operations.Project
public import CORALean.ContSet.SpectraShadow.Float.Operations.Inter
public import CORALean.ContSet.SpectraShadow.Float.Operations.AbsorbRounding
public import CORALean.ContSet.SpectraShadow.Float.Operations.ContainsPoint
public import CORALean.ContSet.SpectraShadow.Float.Operations.Base
public import CORALean.ContSet.SpectraShadow.Float.Operations.DualBound
public import CORALean.ContSet.SpectraShadow.Float.Operations.DualCertified
public import CORALean.ContSet.SpectraShadow.Float.Operations.IsBounded
public import CORALean.ContSet.SpectraShadow.Float.Operations.RepresentsaEmptySet
public import CORALean.ContSet.SpectraShadow.Float.Operations.RepresentsaOrigin
public import CORALean.ContSet.SpectraShadow.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.SpectraShadow.Float.Operations.ArrowMat
public import CORALean.ContSet.SpectraShadow.Float.Operations.Cone
public import CORALean.ContSet.SpectraShadow.Float.Operations.SingletonOne
public import CORALean.ContSet.SpectraShadow.Float.Operations.HyperplaneOne
public import CORALean.ContSet.SpectraShadow.Float.Operations.ConvHull
public import CORALean.ContSet.SpectraShadow.Float.Operations.Or
public import CORALean.ContSet.SpectraShadow.Float.Operations.PolytopeOuter
public import CORALean.ContSet.SpectraShadow.Float.Operations.Materialise
public import CORALean.ContSet.SpectraShadow.Float.Operations.IsFullDim

/-!
# What a float spectrahedral shadow computes, collected

`plus`, which lays the two inequalities along a diagonal and rounds only the
center, with `centerResidual` the box that rounding costs.

`Inf` and `empty`, the two constant `1 × 1` inequalities with the origin box, and
`project`, which reads the stored center and generator rows at the chosen coordinates.

`mtimes` ties the point to new free variables and multiplies only the error box, so no stored
generator is rounded; `cartProd`, `inter` and `convHull_` (and `or`) are built from the same
exact pieces, with `plus` rounding the center alone.
-/
