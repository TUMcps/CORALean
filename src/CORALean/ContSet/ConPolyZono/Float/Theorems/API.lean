import CORALean.ContSet.ConPolyZono.Float.Theorems.IsequalSound
import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionD
import CORALean.ContSet.ConPolyZono.Float.Theorems.ProjectOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealAgreeRow
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatIntersectionA
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalIntersectionB
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalIntersectionDep
import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionDepOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.SplitOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.Merge
import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactGensOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactConsOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsNominal
import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalDependent
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalSetDependent
import CORALean.ContSet.ConPolyZono.Float.Theorems.DependentExact
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA
import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealVecAppend
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalPlusB
import CORALean.ContSet.ConPolyZono.Float.Theorems.SatisfiesPlusIff
import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusH
import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.SatisfiesLinCombIff
import CORALean.ContSet.ConPolyZono.Float.Theorems.LinCombOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.MtimesH
import CORALean.ContSet.ConPolyZono.Float.Theorems.SatisfiesMtimes
import CORALean.ContSet.ConPolyZono.Float.Theorems.MtimesOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceByOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceGirardOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceGirardOrderLe
import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceOrder
import CORALean.ContSet.ConPolyZono.Float.Theorems.IsCompact
import CORALean.ContSet.ConPolyZono.Float.Theorems.OriginExact
import CORALean.ContSet.ConPolyZono.Float.Theorems.ReindexExact
import CORALean.ContSet.ConPolyZono.Float.Theorems.EmptyExact
import CORALean.ContSet.ConPolyZono.Float.Theorems.CartProdExact
import CORALean.ContSet.ConPolyZono.Float.Theorems.GetSubsetOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.SplitDepFactorOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.SplitLongestGenOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.CentreMemConstruct
import CORALean.ContSet.ConPolyZono.Float.Theorems.RepresentsaPointSubset
import CORALean.ContSet.ConPolyZono.Float.Theorems.SupportBoundLe
import CORALean.ContSet.ConPolyZono.Float.Theorems.MinkDiffOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.ExactPlusOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.QuadMapOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionConIntEq
import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionUpperHolds
import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionLowerHolds
import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionSatisfies
import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionPointMem
import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.ConvHullSatisfies
import CORALean.ContSet.ConPolyZono.Float.Theorems.ConvHullSingleOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.ConvHullOuter
import CORALean.ContSet.ConPolyZono.Float.Theorems.IsFullDimSound

/-!
# What `ConPolyZono` guarantees

The exact layer's `plus`, `map`, `intersection`, `compact` and `reduce` read as
enclosures, `dependent` still exactly. `reduce_order_le` is the one guarantee
here that is not an enclosure, and the one this layer needs most: an unbounded
generator count is memory and time per step.

`compact_outer` is the one that moves the counts, and the one that widens `b`:
merging a constraint column rounds, and `b` is the only place on that side a
rounding can go, the state's error box being of the wrong dimension.

`plus` and `mtimes` rest on the constraint block surviving `toReal`:
`satisfies_plus_iff` is the exact layer's `holds_plus_iff` at the read-back
matrices, and `satisfies_mtimes` is `Iff.rfl`.

`intersection_outer` is the one that computes a constraint, and it is the file to read.
The two nominal points it has to make agree differ by whatever the two error
boxes admit, so the agreement rows carry an interval wide enough for that
difference — which leaves the rounding of the centres nowhere to go but into an
interval that was going to be widened anyway. `MemNominalSet` is how each of
them reads the nominal half of a point.
-/
