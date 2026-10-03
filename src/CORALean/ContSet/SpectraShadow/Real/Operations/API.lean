import CORALean.ContSet.SpectraShadow.Real.Operations.Plus
import CORALean.ContSet.SpectraShadow.Real.Operations.Map
import CORALean.ContSet.SpectraShadow.Real.Operations.Mtimes
import CORALean.ContSet.SpectraShadow.Real.Operations.CartProd
import CORALean.ContSet.SpectraShadow.Real.Operations.Empty
import CORALean.ContSet.SpectraShadow.Real.Operations.Inf
import CORALean.ContSet.SpectraShadow.Real.Operations.Project
import CORALean.ContSet.SpectraShadow.Real.Operations.Inter

/-!
# What a spectrahedral shadow computes, collected

`plus`, which lays the two inequalities along a diagonal; `map`, a linear image,
and `mtimes` and `cartProd` after it, the first at a matrix and the second at the
two embeddings into a product, and `inter`, `plus` with the two points forced equal. All five
are exact and none solves a semidefinite program.
-/
