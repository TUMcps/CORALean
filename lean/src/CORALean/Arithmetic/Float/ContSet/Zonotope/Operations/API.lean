import CORALean.Arithmetic.Float.ContSet.Zonotope.Operations.GeneratorError
import CORALean.Arithmetic.Float.ContSet.Zonotope.Operations.Plus
import CORALean.Arithmetic.Float.ContSet.Zonotope.Operations.LinComb
import CORALean.Arithmetic.Float.ContSet.Zonotope.Operations.Mtimes
import CORALean.Arithmetic.Float.ContSet.Zonotope.Operations.Interval
import CORALean.Arithmetic.Float.ContSet.Zonotope.Operations.AbsorbError
import CORALean.Arithmetic.Float.ContSet.Zonotope.Operations.Reduce
import CORALean.Arithmetic.Float.ContSet.Zonotope.Operations.ReduceAndAbsorb

/-!
# What `Zonotope` computes

One file per operation, named as CORA names it. Each pays its rounding into the
error box rather than into new generators, except where a diagonal block is
being appended anyway.
-/
