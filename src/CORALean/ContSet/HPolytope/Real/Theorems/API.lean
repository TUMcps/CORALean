import CORALean.ContSet.HPolytope.Real.Theorems.AndExact
import CORALean.ContSet.HPolytope.Real.Theorems.BoxExact
import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact
import CORALean.ContSet.HPolytope.Real.Theorems.Convex
import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
import CORALean.ContSet.HPolytope.Real.Theorems.MapEquivExact
import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact

/-!
# What `HPolytope` guarantees

Every operation exactly — a halfspace description approximates nothing, the loss
being in what it cannot compute at all. Convex and closed, but not bounded:
unbounded is what this representation admits and a vertex one cannot.
-/
