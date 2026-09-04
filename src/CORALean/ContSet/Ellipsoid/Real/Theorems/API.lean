import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.QMemConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqImage
import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsBounded
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
import CORALean.ContSet.Ellipsoid.Real.Theorems.MapExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusOuter
import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained

/-!
# What an ellipsoid guarantees, collected

Exact under a linear image; enclosing under a Minkowski sum, and only ever
enclosing there. `SupportBoundAttained` is what says the certificates give
nothing away, and convexity, compactness and boundedness are what the
reachability theorems consume. `ConstructEqImage` is what all three of those
last transfer from the unit ball through.
-/
