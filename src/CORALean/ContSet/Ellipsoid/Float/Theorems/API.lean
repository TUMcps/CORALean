import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesK
import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesOuter
import CORALean.ContSet.Ellipsoid.Float.Theorems.PlusK
import CORALean.ContSet.Ellipsoid.Float.Theorems.PlusOuter

/-!
# What a float ellipsoid guarantees, collected

Enclosing under a linear image, where the exact layer is exact, and enclosing
under a Minkowski sum, where it already was. `MemGeneratorError` is what both
pay their rounding through, and `MemNominalSet` is how each reads the nominal
half of a point.
-/
