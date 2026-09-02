import CORALean.ContSet.Zonotope.Real.Operations.GenMap
import CORALean.ContSet.Zonotope.Real.Operations.Map
import CORALean.ContSet.Zonotope.Real.Operations.LinMtimes
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Operations.Reduce

/-!
# What `Zonotope` computes

Only `reduce` bounds the generator count; the others grow it freely.
-/
