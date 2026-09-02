import CORALean.ContSet.ConPolyZono.Real.Theorems.AndExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.PlusExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.QuadMapExact

/-!
# What `ConPolyZono` guarantees

`and`, `plus`, `map`, `quadMap` and `dependent`, all five exactly. Nothing here
is an enclosure, which is unusual and is the constraints paying for themselves:
the operations that would have to relax something are the ones left out.

`and_exact` is the one that distinguishes the representation. It is the only
exact intersection in this repository that is not of convex sets, and together
with `quadMap_exact` it is what a nonlinear reachability step needs: propagate
through a quadratic map, then cut by a guard, neither losing anything.
-/
