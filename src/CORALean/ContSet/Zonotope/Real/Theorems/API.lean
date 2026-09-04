import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMulLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.LmtimesSingletonOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulLeftExact
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulRightExact
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallEq
import CORALean.ContSet.Zonotope.Real.Theorems.ContinuousAffine
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffSum
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffDiff
import CORALean.ContSet.Zonotope.Real.Theorems.AbsWeightedLe
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffSumLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffDiffLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.SumPair
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Real.Theorems.SumUnivReduceBy
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceCombastelOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

/-!
# What `Zonotope` guarantees

`plus` and `map` exactly, `reduce` and the interval hull as enclosures, and the
topological facts a set-valued integral needs. `MemConstruct` reads membership
coordinatewise, which is what every one of them is stated against, and
`Coefficient` with the two facts about it holds the shared proof devices, which
the float layer needs too.
-/
