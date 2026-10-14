module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.IsequalSound
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionD
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ProjectOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealAgreeRow
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatIntersectionA
public import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalIntersectionB
public import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalIntersectionDep
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionDepOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.SplitOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.Merge
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactGensEqSpec
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactGensOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactConsEqSpec
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactConsOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsEqSpec
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsNominal
public import CORALean.ContSet.ConPolyZono.Float.Theorems.Basic
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalDependent
public import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalSetDependent
public import CORALean.ContSet.ConPolyZono.Float.Theorems.DependentExact
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA
public import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalPlusB
public import CORALean.ContSet.ConPolyZono.Float.Theorems.SatisfiesPlusIff
public import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.SatisfiesLinCombIff
public import CORALean.ContSet.ConPolyZono.Float.Theorems.LinCombOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.SatisfiesMtimes
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MtimesOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceByOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceGirardOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceGirardOrderLe
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceOrder
public import CORALean.ContSet.ConPolyZono.Float.Theorems.OriginExact
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReindexExact
public import CORALean.ContSet.ConPolyZono.Float.Theorems.EmptyExact
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CartProdExact
public import CORALean.ContSet.ConPolyZono.Float.Theorems.GetSubsetSatisfies
public import CORALean.ContSet.ConPolyZono.Float.Theorems.GetSubsetOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.GetSubsetPointOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.RescaleOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.SplitDepFactorOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.SplitLongestGenOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CentreMemConstruct
public import CORALean.ContSet.ConPolyZono.Float.Theorems.RepresentsaPointSubset
public import CORALean.ContSet.ConPolyZono.Float.Theorems.SupportBoundLe
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MinkDiffOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ExactPlusOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionConIntEq
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionUpperHolds
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionLowerHolds
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionSatisfies
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionPointMem
public import CORALean.ContSet.ConPolyZono.Float.Theorems.UnionOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ConvHullSatisfies
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ConvHullSingleOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ConvHullOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IsFullDimSound

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
