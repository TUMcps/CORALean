import CORALean.ContSet.HPolytope.Real.Theorems.MemConstruct
import CORALean.ContSet.HPolytope.Real.Theorems.MemAnd
import CORALean.ContSet.HPolytope.Real.Theorems.AndExact
import CORALean.ContSet.HPolytope.Real.Theorems.PlusOfOuter
import CORALean.ContSet.HPolytope.Real.Theorems.MinkDiffOfInner
import CORALean.ContSet.HPolytope.Real.Theorems.LinCombOfOuter
import CORALean.ContSet.HPolytope.Real.Theorems.MtimesOfOuter
import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact
import CORALean.ContSet.HPolytope.Real.Theorems.Convex
import CORALean.ContSet.HPolytope.Real.Theorems.ExtremePoints
import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
import CORALean.ContSet.HPolytope.Real.Theorems.MapEquivExact
import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact
import CORALean.ContSet.HPolytope.Real.Theorems.OfPointMem

/-!
# What `HPolytope` guarantees

The operations whose rows the inputs determine, exactly; the rest enclosing,
each in one line off `subset_ofBounds`. Convex and closed, but not bounded:
unbounded is what this representation admits and a vertex one cannot.
`MemConstruct` names the pair of constraint blocks every one of them is stated
against. `MinkDiffOfInner` is the one guarantee running the other way: an inner
approximation of the Minkowski difference, needing `hker` on the equality rows.
`OfPointMem` is the one at `Vec ℝ n` alone, `LinearMap.proj` needing coordinates.
-/
