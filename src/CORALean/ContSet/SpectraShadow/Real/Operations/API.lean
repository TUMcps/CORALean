module

public import CORALean.ContSet.SpectraShadow.Real.Operations.Plus
public import CORALean.ContSet.SpectraShadow.Real.Operations.Map
public import CORALean.ContSet.SpectraShadow.Real.Operations.Mtimes
public import CORALean.ContSet.SpectraShadow.Real.Operations.CartProd
public import CORALean.ContSet.SpectraShadow.Real.Operations.Empty
public import CORALean.ContSet.SpectraShadow.Real.Operations.Inf
public import CORALean.ContSet.SpectraShadow.Real.Operations.Project
public import CORALean.ContSet.SpectraShadow.Real.Operations.Inter
public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc
public import CORALean.ContSet.SpectraShadow.Real.Operations.IsBounded
public import CORALean.ContSet.SpectraShadow.Real.Operations.ContainsPoint
public import CORALean.ContSet.SpectraShadow.Real.Operations.ContainsPointCora
public import CORALean.ContSet.SpectraShadow.Real.Operations.LineExample
public import CORALean.ContSet.SpectraShadow.Real.Operations.PointExample
public import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaFullspaceCora
public import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaOrigin
public import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportBound
public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFuncCoraAllZero
public import CORALean.ContSet.SpectraShadow.Real.Operations.ArrowMat
public import CORALean.ContSet.SpectraShadow.Real.Operations.Cone
public import CORALean.ContSet.SpectraShadow.Real.Operations.SingletonOne
public import CORALean.ContSet.SpectraShadow.Real.Operations.HyperplaneOne
public import CORALean.ContSet.SpectraShadow.Real.Operations.ConvHull
public import CORALean.ContSet.SpectraShadow.Real.Operations.Or
public import CORALean.ContSet.SpectraShadow.Real.Operations.Translate
public import CORALean.ContSet.SpectraShadow.Real.Operations.PolytopeOuter
public import CORALean.ContSet.SpectraShadow.Real.Operations.PolytopeInner
public import CORALean.ContSet.SpectraShadow.Real.Operations.GFro
public import CORALean.ContSet.SpectraShadow.Real.Operations.FullDimShortcut
public import CORALean.ContSet.SpectraShadow.Real.Operations.GenerateESumRep

/-!
# What a spectrahedral shadow computes, collected

`plus`, which lays the two inequalities along a diagonal; `map`, a linear image,
and `mtimes` and `cartProd` after it, the first at a matrix and the second at the
two embeddings into a product, and `inter`, `plus` with the two points forced equal. All five
are exact and none solves a semidefinite program. `supportFunc`, `isBounded`, `representsa_` and
`containsPoint` are specifications of the semidefinite programs CORA solves, and `supportBound`
the weak-duality certificate that bounds one of them without a solver.
-/
