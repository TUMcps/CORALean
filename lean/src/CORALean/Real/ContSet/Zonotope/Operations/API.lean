import CORALean.Real.ContSet.Zonotope.Operations.Plus
import CORALean.Real.ContSet.Zonotope.Operations.Mtimes
import CORALean.Real.ContSet.Zonotope.Operations.Interval
import CORALean.Real.ContSet.Zonotope.Operations.MtimesIntervalMat
import CORALean.Real.ContSet.Zonotope.Operations.LinComb
import CORALean.Real.ContSet.Zonotope.Operations.Reduce

/-!
# What `Zonotope` computes

One file per operation, named as CORA names it. Only `reduce` bounds the
generator count; the others grow it freely.
-/
