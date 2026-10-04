import CORALean.ContSet.SpectraShadow.Real.Operations.Plus
import CORALean.ContSet.SpectraShadow.Real.Operations.Map
import CORALean.ContSet.SpectraShadow.Real.Operations.Mtimes
import CORALean.ContSet.SpectraShadow.Real.Operations.CartProd
import CORALean.ContSet.SpectraShadow.Real.Operations.Empty
import CORALean.ContSet.SpectraShadow.Real.Operations.Inf
import CORALean.ContSet.SpectraShadow.Real.Operations.Project
import CORALean.ContSet.SpectraShadow.Real.Operations.Inter
import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc
import CORALean.ContSet.SpectraShadow.Real.Operations.IsBounded
import CORALean.ContSet.SpectraShadow.Real.Operations.ContainsPoint
import CORALean.ContSet.SpectraShadow.Real.Operations.ContainsPointCora
import CORALean.ContSet.SpectraShadow.Real.Operations.LineExample
import CORALean.ContSet.SpectraShadow.Real.Operations.PointExample
import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaFullspaceCora
import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaPoint
import CORALean.ContSet.SpectraShadow.Real.Operations.SupportBound
import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFuncCoraAllZero

/-!
# What a spectrahedral shadow computes, collected

`plus`, which lays the two inequalities along a diagonal; `map`, a linear image,
and `mtimes` and `cartProd` after it, the first at a matrix and the second at the
two embeddings into a product, and `inter`, `plus` with the two points forced equal. All five
are exact and none solves a semidefinite program. `supportFunc`, `isBounded`, `representsa_` and
`containsPoint` are specifications of the semidefinite programs CORA solves, and `supportBound`
the weak-duality certificate that bounds one of them without a solver.
-/
