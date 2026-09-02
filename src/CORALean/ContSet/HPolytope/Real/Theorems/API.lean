import CORALean.ContSet.HPolytope.Real.Theorems.AndExact
import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact
import CORALean.ContSet.HPolytope.Real.Theorems.Convex
import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed

/-!
# What `HPolytope` guarantees

Both operations exactly — a halfspace description approximates nothing, the loss
being in what it cannot compute at all. Convex and closed, but not bounded:
unbounded is what this representation admits and a vertex one cannot.
-/
