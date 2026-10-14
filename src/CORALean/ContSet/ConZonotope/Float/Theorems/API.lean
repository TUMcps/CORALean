module

public import CORALean.ContSet.ConZonotope.Float.Theorems.IsequalSound
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.ProjectOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceLiftByOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceLiftOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.UnionSubsetLinComb
public import CORALean.ContSet.ConZonotope.Float.Theorems.ConvexHullSubsetLinComb
public import CORALean.ContSet.ConZonotope.Float.Theorems.Basic
public import CORALean.ContSet.ConZonotope.Float.Theorems.EmptyExact
public import CORALean.ContSet.ConZonotope.Float.Theorems.OriginExact
public import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.SplitOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.ReindexExact
public import CORALean.ContSet.ConZonotope.Float.Theorems.BoundDotLe
public import CORALean.ContSet.ConZonotope.Float.Theorems.BoundDotWeightsLe
public import CORALean.ContSet.ConZonotope.Float.Theorems.SeparatesAlongSound
public import CORALean.ContSet.ConZonotope.Float.Theorems.IsDisjointLPSound
public import CORALean.ContSet.ConZonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.ConZonotope.Float.Theorems.MinkDiffVOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.ConIntersectOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.RescaleOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.CompactExact
public import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectStripOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.DependentNominal
public import CORALean.ContSet.ConZonotope.Float.Theorems.QuadBilBracket
public import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapGClose
public import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapCBetween
public import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapDepNominal
public import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.BoxSubset
public import CORALean.ContSet.ConZonotope.Float.Theorems.CentreBetween
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemInterior
public import CORALean.ContSet.ConZonotope.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.ConZonotope.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.ConZonotope.Float.Theorems.RepresentsaEmptySetSound
public import CORALean.ContSet.ConZonotope.Float.Theorems.ConstructEqNominal
public import CORALean.ContSet.ConZonotope.Float.Theorems.LinCombSameCentreSubset
public import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesNominalErr
public import CORALean.ContSet.ConZonotope.Float.Theorems.ZeroFeasibleNonempty
public import CORALean.ContSet.ConZonotope.Float.Theorems.CubMapOuter

/-!
# What the float `ConZonotope` guarantees

Each operation encloses what the exact one does. The constraints cost nothing to
carry through `plus`, padding being exact, nor through `linComb`, where
weighting a row halves its right-hand side and halving is exact too; in both the
only rounding is the centre's, and the box absorbs it as a zonotope's does.
`MemNominalSet` is how each of them reads the nominal half of a point.
-/
