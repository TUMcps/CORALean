import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsPointIff
import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsMono
import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsCongr
import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConstruct
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
import CORALean.ContSet.ConPolyZono.Real.Theorems.AndDepExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.AndExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactGensExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactConsExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactFactorsExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.MtimesExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.PlusExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.QuadMapDepExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.QuadMapExact

/-!
# What `ConPolyZono` guarantees

`and`, `plus`, `map`, `quadMap`, `dependent` and `compact`, all six exactly.
Nothing here is an enclosure, which is unusual and is the constraints paying for
themselves: the operations that would have to relax something are the ones left
out.

`compact_exact` is three equalities in a row and no hypothesis anywhere, which
is what makes it bookkeeping: merging the generators, merging the constraint
columns, and dropping the factors neither block reads.

`and_exact` is the one that distinguishes the representation. It is the only
exact intersection in this repository that is not of convex sets, and together
with `quadMap_exact` it is what a nonlinear reachability step needs: propagate
through a quadratic map, then cut by a guard, neither losing anything.

What `holds` satisfies, and `MemConstruct`, are what all six are stated over.
-/
