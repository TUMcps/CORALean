import CORALean.ContSet.HPolytope.Theorems.AndExact
import CORALean.ContSet.HPolytope.Theorems.ComapExact
import CORALean.ContSet.HPolytope.Theorems.Convex
import CORALean.ContSet.HPolytope.Theorems.IsClosed

/-!
# What `HPolytope` guarantees

Both operations exactly — a halfspace description approximates nothing, the loss
being in what it cannot compute at all. Convex and closed, but not bounded:
unbounded is what this representation admits and a vertex one cannot.
-/
