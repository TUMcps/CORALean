import CORALean.ContSet.Zonotope.Real.Operations.GenMap
import CORALean.ContSet.Zonotope.Real.Operations.Map
import CORALean.ContSet.Zonotope.Real.Operations.LinMtimes
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.MtimesEqMap
import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
import CORALean.ContSet.Zonotope.Real.Operations.RadiusReach
import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Operations.Bilin
import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope
import CORALean.ContSet.Zonotope.Real.Operations.PairSum
import CORALean.ContSet.Zonotope.Real.Operations.PairDiff
import CORALean.ContSet.Zonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
import CORALean.ContSet.Zonotope.Real.Operations.ReduceCombastel
import CORALean.ContSet.Zonotope.Real.Operations.Reduce

/-!
# What `Zonotope` computes

Only `reduce` bounds the generator count; the others grow it freely. `bilin`
and `mtimesMatZonotope` are a matrix zonotope acting on a set, at any bilinear
map and at `Matrix.mulVecBilin` respectively.
-/
