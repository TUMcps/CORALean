import CORALean.ContSet.SpectraShadow.Float.Operations.CenterResidual
import CORALean.ContSet.SpectraShadow.Float.Operations.Empty
import CORALean.ContSet.SpectraShadow.Float.Operations.Inf
import CORALean.ContSet.SpectraShadow.Float.Operations.Plus
import CORALean.ContSet.SpectraShadow.Float.Operations.Project

/-!
# What a float spectrahedral shadow computes, collected

`plus`, which lays the two inequalities along a diagonal and rounds only the
centre, with `centerResidual` the box that rounding costs.

`Inf` and `empty`, the two constant `1 × 1` inequalities with the origin box, and
`project`, which reads the stored centre and generator rows at the chosen coordinates.

`mtimes` and `cartProd` are absent. The first rounds every generator, and a
generator's rounding multiplies a variable the inequality leaves unbounded, so no
box holds it. The second is absent as in every float representation: the product
lives in another ambient dimension, which only `Mtimes` crosses.
-/
