import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsPointIff
import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsMono
import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsCongr
import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConstruct
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionDepExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactGensExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactConsExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactFactorsExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.MtimesExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.OfPointMem
import CORALean.ContSet.ConPolyZono.Real.Theorems.PlusExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CartProdExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.LinCombOuter
import CORALean.ContSet.ConPolyZono.Real.Theorems.LinCombExactOfDependent
import CORALean.ContSet.ConPolyZono.Real.Theorems.QuadMapDepExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.QuadMapExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.ConstructEqImage
import CORALean.ContSet.ConPolyZono.Real.Theorems.ContinuousAffine
import CORALean.ContSet.ConPolyZono.Real.Theorems.IsCompactDomain
import CORALean.ContSet.ConPolyZono.Real.Theorems.IsCompact
import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceByOuter
import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceGirardOuter
import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceOuter
import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceGirardOrderLe
import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceOrder
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentSetUnionDomain
import CORALean.ContSet.ConPolyZono.Real.Theorems.GetSubsetConstruct
import CORALean.ContSet.ConPolyZono.Real.Theorems.UnionDomainIff
import CORALean.ContSet.ConPolyZono.Real.Theorems.UnionExact

/-!
# What `ConPolyZono` guarantees

`intersection`, `plus`, `map`, `quadMap`, `dependent` and `compact`, all six exactly, and
`reduce` as an enclosure with an order bound beside it — the only operation here
that gives anything up, and the only one that has to.

`compact_exact` is three equalities in a row and no hypothesis anywhere, which
is what makes it bookkeeping: merging the generators, merging the constraint
columns, and dropping the factors neither block reads. `reduce_order_le` is what
that bookkeeping is for.

`intersection_exact` is the one that distinguishes the representation. It is the only
exact intersection in this repository that is not of convex sets, and together
with `quadMap_exact` it is what a nonlinear reachability step needs: propagate
through a quadratic map, then cut by a guard, neither losing anything.

`isCompact_construct` is the one guarantee about the set rather than an operation:
a constraint row is a polynomial in the factors, so it closes the domain rather
than opening it. `holds` and `MemConstruct` are what the operations are stated over.

`mem_ofPoint` needs none of that, and `getSubset_construct` is an equality, its
substitution a polynomial identity. So is `union_exact_of_noZeroCol` — under a
hypothesis the source omits and is false without, which its own file sets out.
-/
