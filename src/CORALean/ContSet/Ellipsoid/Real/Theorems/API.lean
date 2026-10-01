import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.QMemConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqImage
import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsBounded
import CORALean.ContSet.Ellipsoid.Real.Theorems.ContinuousAffine
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsClosed
import CORALean.ContSet.Ellipsoid.Real.Theorems.MapExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact
import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusOuter
import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusScalingsAdmissible
import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
import CORALean.ContSet.Ellipsoid.Real.Theorems.IsGreatestSupport
import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMem
import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Ellipsoid.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.ProjectExact

/-!
# What an ellipsoid guarantees, collected

Exact under a linear image; enclosing under a Minkowski sum, and only ever
enclosing there — at every admissible pair of scalings, of which
`PlusScalingsAdmissible` picks out the curve Kurzhanski and Varaiya's `l`
sweeps. `SupportBoundAttained` is what says the certificates give nothing away,
and convexity, compactness and boundedness are what the reachability theorems
consume. `ConstructEqImage` is what all three of those last transfer from the
unit ball through. `mem_ofPoint` reuses `mem_construct` at the empty
coefficient vector.
-/
