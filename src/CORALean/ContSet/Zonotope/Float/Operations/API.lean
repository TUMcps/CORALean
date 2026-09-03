import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError
import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.LinComb
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Operations.AbsorbError
import CORALean.ContSet.Zonotope.Float.Operations.Reduce
import CORALean.ContSet.Zonotope.Float.Operations.ReduceAndAbsorb
import CORALean.ContSet.Zonotope.Float.Operations.Reindex

/-!
# What `Zonotope` computes

Each pays its rounding into the error box rather than into new generators,
except where a diagonal block is being appended anyway.
-/
