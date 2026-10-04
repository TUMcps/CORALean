import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.RadiusLe
import CORALean.ContSet.Zonotope.Float.Theorems.GeneratorLengthLe
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Float.Theorems.AbsLeAbsBoundError
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesMatZonotopeOuter
import CORALean.ContSet.Zonotope.Float.Theorems.OfEntryBoundsOuter
import CORALean.ContSet.Zonotope.Float.Theorems.PlusH
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.PlusSubsetAddBox
import CORALean.ContSet.Zonotope.Float.Theorems.ProjectHighDimOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ProjectOuter
import CORALean.ContSet.Zonotope.Float.Theorems.RecentreSubMem
import CORALean.ContSet.Zonotope.Float.Theorems.RecentreZeroMem
import CORALean.ContSet.Zonotope.Float.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombH
import CORALean.ContSet.Zonotope.Float.Theorems.PairSumBracket
import CORALean.ContSet.Zonotope.Float.Theorems.PairDiffBracket
import CORALean.ContSet.Zonotope.Float.Theorems.SumPairMul
import CORALean.ContSet.Zonotope.Float.Theorems.MidpointMemResidual
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesH
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesSubsetAddBox
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Float.Theorems.RotMatMem
import CORALean.ContSet.Zonotope.Float.Theorems.RotateOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemMtimesError
import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemPlusError
import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbErrorH
import CORALean.ContSet.Zonotope.Float.Theorems.AbsSubMidLeErrorRadius
import CORALean.ContSet.Zonotope.Float.Theorems.ShiftBracketsMid
import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbErrorOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuterRefines
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByH
import CORALean.ContSet.Zonotope.Float.Theorems.AbsAbsorbedLeRadius
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceBySubsetAddBox
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceCombastelOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceSubsetAddBox
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOrder
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAndAbsorbByH
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAndAbsorbByOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReindexNominal
import CORALean.ContSet.Zonotope.Float.Theorems.ReindexExact
import CORALean.ContSet.Zonotope.Float.Theorems.Convex
import CORALean.ContSet.Zonotope.Float.Theorems.UnionSubsetLinComb
import CORALean.ContSet.Zonotope.Float.Theorems.ConvexHullSubsetLinComb
import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Float.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Float.Theorems.ConstrSatSound
import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
import CORALean.ContSet.Zonotope.Float.Theorems.OriginExact
import CORALean.ContSet.Zonotope.Float.Theorems.NormSqLe
import CORALean.ContSet.Zonotope.Float.Theorems.SplitOuter
import CORALean.ContSet.Zonotope.Float.Theorems.SplitFirstGenOuter
import CORALean.ContSet.Zonotope.Float.Theorems.SplitLongestGenOuter
import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapOuter
import CORALean.ContSet.Zonotope.Float.Theorems.NominalCartProdC
import CORALean.ContSet.Zonotope.Float.Theorems.NominalCartProdG
import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
import CORALean.ContSet.Zonotope.Float.Theorems.ExactPlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.Zonotope.Float.Theorems.RepresentsaOriginSound
import CORALean.ContSet.Zonotope.Float.Theorems.AndOuter
import CORALean.ContSet.Zonotope.Float.Theorems.IsequalSound
import CORALean.ContSet.Zonotope.Float.Theorems.CompactZerosExact
import CORALean.ContSet.Zonotope.Float.Theorems.IntersectStripOuter
import CORALean.ContSet.Zonotope.Float.Theorems.AbsCornerMem
import CORALean.ContSet.Zonotope.Float.Theorems.AbsNominal
import CORALean.ContSet.Zonotope.Float.Theorems.AbsCornerMemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.AbsLeAbsBoundNominalSet

/-!
# What `Zonotope` guarantees

Stated exactly as `Real` states it, over the same sets of real points and with
the same generator counts — rounding is paid into the error box, so no operation
but `absorbError` spends a generator on it. `MemNominalSet` is what every one of
them reads the nominal half of a point in.

`Convex`, `IsCompact` and `IsClosed` are the exception: their exact-layer
counterparts do not transfer, the set here being a nominal one plus a box.

`SubsetAddBox` and `ZeroMem*Error` are the reverse direction: how far `plus`,
`mtimes` and `reduce` reach *beyond* their operand, what `reachErrorFloat`
accumulates.
-/
