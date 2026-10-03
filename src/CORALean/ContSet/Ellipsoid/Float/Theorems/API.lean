import CORALean.ContSet.Ellipsoid.Float.Theorems.BoundDotLe
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
import CORALean.ContSet.Ellipsoid.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesK
import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesOuter
import CORALean.ContSet.Ellipsoid.Float.Theorems.PlusK
import CORALean.ContSet.Ellipsoid.Float.Theorems.PlusOuter
import CORALean.ContSet.Ellipsoid.Float.Theorems.ProjectOuter
import CORALean.ContSet.Ellipsoid.Float.Theorems.Convex
import CORALean.ContSet.Ellipsoid.Float.Theorems.IsCompact
import CORALean.ContSet.Ellipsoid.Float.Theorems.OriginExact
import CORALean.ContSet.Ellipsoid.Float.Theorems.CentreMemConstruct
import CORALean.ContSet.Ellipsoid.Float.Theorems.ReindexExact
import CORALean.ContSet.Ellipsoid.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.Ellipsoid.Float.Theorems.RepresentsaOriginSound
import CORALean.ContSet.Ellipsoid.Float.Theorems.IsequalSound
import CORALean.ContSet.Ellipsoid.Float.Theorems.VerticesOuter
import CORALean.ContSet.Ellipsoid.Float.Theorems.NormUbLe
import CORALean.ContSet.Ellipsoid.Float.Theorems.CartProdOuter
import CORALean.ContSet.Ellipsoid.Float.Theorems.CartProdVecExact

/-!
# What a float ellipsoid guarantees, collected

Enclosing under a linear image, where the exact layer is exact, and enclosing
under a Minkowski sum, where it already was. `MemGeneratorError` is what both
pay their rounding through, and `MemNominalSet` is how each reads the nominal
half of a point.
-/
