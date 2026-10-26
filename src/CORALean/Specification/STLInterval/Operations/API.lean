module

public import CORALean.Specification.STLInterval.Operations.And
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.ContainsFloat
public import CORALean.Specification.STLInterval.Operations.Infimum
public import CORALean.Specification.STLInterval.Operations.Interval
public import CORALean.Specification.STLInterval.Operations.IsequalFloat
public import CORALean.Specification.STLInterval.Operations.MinkDiff
public import CORALean.Specification.STLInterval.Operations.Minus
public import CORALean.Specification.STLInterval.Operations.MinusInterval
public import CORALean.Specification.STLInterval.Operations.MinusInward
public import CORALean.Specification.STLInterval.Operations.MinusNum
public import CORALean.Specification.STLInterval.Operations.Plus
public import CORALean.Specification.STLInterval.Operations.PlusInterval
public import CORALean.Specification.STLInterval.Operations.PlusNum
public import CORALean.Specification.STLInterval.Operations.RepresentsaFloat
public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.Operations.StlIntervalBounds
public import CORALean.Specification.STLInterval.Operations.Supremum
public import CORALean.Specification.STLInterval.Operations.ToLeft
public import CORALean.Specification.STLInterval.Operations.ToRealInterval
public import CORALean.Specification.STLInterval.Operations.ToRight
public import CORALean.Specification.STLInterval.Operations.WithinTolFloat

/-!
# STL intervals: the operations

The methods of `@stlInterval`: the constructor `stlInterval`, `and_`, `plus`, `minus` and
`minkDiff` (each with its `interval` and numeric variants where CORA has them), `toLeft`,
`toRight`, the closures, `infimum`, `supremum` and `interval`. `minkDiffCora` is `minkDiff` as
printed, `Inf - Inf = NaN` included.
-/
