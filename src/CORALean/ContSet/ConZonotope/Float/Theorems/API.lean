import CORALean.ContSet.ConZonotope.Float.Theorems.IsequalSound
import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConZonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ProjectOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceLiftByOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceLiftOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.UnionSubsetLinComb
import CORALean.ContSet.ConZonotope.Float.Theorems.ConvexHullSubsetLinComb
import CORALean.ContSet.ConZonotope.Float.Theorems.Convex
import CORALean.ContSet.ConZonotope.Float.Theorems.EmptyExact
import CORALean.ContSet.ConZonotope.Float.Theorems.IsCompact
import CORALean.ContSet.ConZonotope.Float.Theorems.OriginExact
import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.SplitOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ReindexExact
import CORALean.ContSet.ConZonotope.Float.Theorems.BoundDotLe
import CORALean.ContSet.ConZonotope.Float.Theorems.BoundDotWeightsLe
import CORALean.ContSet.ConZonotope.Float.Theorems.SeparatesAlongSound
import CORALean.ContSet.ConZonotope.Float.Theorems.IsDisjointLPSound
import CORALean.ContSet.ConZonotope.Float.Theorems.CartProdExact
import CORALean.ContSet.ConZonotope.Float.Theorems.MinkDiffVOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ConIntersectOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.RescaleOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.CompactExact
import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectStripOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.ConZonotope.Float.Theorems.QuadBilBracket
import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapGClose
import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapCBetween
import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapDepNominal
import CORALean.ContSet.ConZonotope.Float.Theorems.QuadMapOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.BoxSubset
import CORALean.ContSet.ConZonotope.Float.Theorems.CentreBetween
import CORALean.ContSet.ConZonotope.Float.Theorems.CornerMem
import CORALean.ContSet.ConZonotope.Float.Theorems.MemInterior
import CORALean.ContSet.ConZonotope.Float.Theorems.ContainsPointSound
import CORALean.ContSet.ConZonotope.Float.Theorems.IsFullDimSound
import CORALean.ContSet.ConZonotope.Float.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.ConZonotope.Float.Theorems.ConstructEqNominal
import CORALean.ContSet.ConZonotope.Float.Theorems.LinCombSameCentreSubset
import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesNominalErr
import CORALean.ContSet.ConZonotope.Float.Theorems.ZeroFeasibleNonempty

/-!
# What the float `ConZonotope` guarantees

Each operation encloses what the exact one does. The constraints cost nothing to
carry through `plus`, padding being exact, nor through `linComb`, where
weighting a row halves its right-hand side and halving is exact too; in both the
only rounding is the centre's, and the box absorbs it as a zonotope's does.
`MemNominalSet` is how each of them reads the nominal half of a point.
-/
