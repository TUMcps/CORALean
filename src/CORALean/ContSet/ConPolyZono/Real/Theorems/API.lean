module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.IsequalConstruct
public import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsPointIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsMono
public import CORALean.ContSet.ConPolyZono.Real.Theorems.HoldsCongr
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemConstruct
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionDepExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactGensExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactConsExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactFactorsExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MtimesExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.OfPointMem
public import CORALean.ContSet.ConPolyZono.Real.Theorems.PlusExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.CartProdExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.LinCombOuter
public import CORALean.ContSet.ConPolyZono.Real.Theorems.LinCombExactOfDependent
public import CORALean.ContSet.ConPolyZono.Real.Theorems.QuadMapDepExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.QuadMapExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ConstructEqImage
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ContinuousAffine
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IsCompactDomain
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IsCompact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceByOuter
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceGirardOuter
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceOuter
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceGirardOrderLe
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceOrder
public import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentSetUnionDomain
public import CORALean.ContSet.ConPolyZono.Real.Theorems.GetSubsetConstruct
public import CORALean.ContSet.ConPolyZono.Real.Theorems.UnionDomainIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.UnionExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceConOuter
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ConvHullSingleConstruct
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ConvHullSingleExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ConvHullExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.Basic
public import CORALean.ContSet.ConPolyZono.Real.Theorems.EmptyExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IsFullDimRank
public import CORALean.ContSet.ConPolyZono.Real.Theorems.SplitDepFactorUnion
public import CORALean.ContSet.ConPolyZono.Real.Theorems.SplitLongestGenUnion
public import CORALean.ContSet.ConPolyZono.Real.Theorems.SplitUnion
public import CORALean.ContSet.ConPolyZono.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ExactPlusConstruct
public import CORALean.ContSet.ConPolyZono.Real.Theorems.RepresentsaPointSubset
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MinkDiffConstruct
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MinkDiffOuter
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MinkDiffInnerOfConvex
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MinkDiffNotInner
public import CORALean.ContSet.ConPolyZono.Real.Theorems.RescaleExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.GetSubsetSatisfies
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ContainsPointIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemExtPolyZonotopeIff

/-!
# What `ConPolyZono` guarantees

`intersection`, `plus`, `map`, `quadMap`, `dependent` and `compact`, all six exactly, and
`reduce` and `reduceCon` as enclosures — the two that give something up, `reduce`
with an order bound beside it.

`compact_exact` is three equalities in a row and no hypothesis anywhere, which is what
makes it bookkeeping: merging the generators, merging the constraint columns, and
dropping the factors neither block reads. `reduce_order_le` is what that is for.

`intersection_exact` is the one that distinguishes the representation. It is the only
exact intersection in this repository that is not of convex sets, and with `quadMap_exact`
it is what a nonlinear reachability step needs: a quadratic map, then a guard, losing
nothing at either.

`isCompact_construct` is the one guarantee about the set rather than an operation: a
constraint row is a polynomial in the factors, so it closes the domain rather than opening
it. `holds` and `MemConstruct` are what the operations are stated over.
`mem_ofPoint` needs none of that, and `getSubset_construct` is an equality, its
substitution a polynomial identity. So are `union_exact_of_noZeroCol` and
`convHull_exact_of_nonempty` — each under a hypothesis the source omits and is false
without, which their own files set out. `reduceCon_outer` substitutes too, and only
encloses: solving a row for a monomial is not reversible once the row is gone.
-/
