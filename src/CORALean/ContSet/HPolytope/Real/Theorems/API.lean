import CORALean.ContSet.HPolytope.Real.Theorems.AndExact
import CORALean.ContSet.HPolytope.Real.Theorems.BoxExact
import CORALean.ContSet.HPolytope.Real.Theorems.CertifiedOuter
import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact
import CORALean.ContSet.HPolytope.Real.Theorems.Convex
import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
import CORALean.ContSet.HPolytope.Real.Theorems.MapEquivExact
import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact

/-!
# What `HPolytope` guarantees

The operations whose rows the inputs determine, exactly; the rest enclosing,
each in one line off `subset_ofBounds`. Convex and closed, but not bounded:
unbounded is what this representation admits and a vertex one cannot.
-/
