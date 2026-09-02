import CORALean.ContSet.Ellipsoid.Float.Operations.GeneratorError
import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes
import CORALean.ContSet.Ellipsoid.Float.Operations.Plus
import CORALean.ContSet.Ellipsoid.Float.Operations.SupportBound

/-!
# What a float ellipsoid computes, collected

`mtimes`, which rounds and pays the difference into the box; `supportBound`,
still closed form and still without a linear program, the square root replaced
by a candidate the caller certifies; `plus`, which takes its free parameter as
two scalings rather than one `l`, there being no division either; and
`generatorError`, what all of them charge a rounded generator.
-/
