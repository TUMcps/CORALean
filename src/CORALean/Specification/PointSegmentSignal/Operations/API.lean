module

public import CORALean.Specification.PointSegmentSignal.Operations.AllTrue
public import CORALean.Specification.PointSegmentSignal.Operations.AnyTrue
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.PointSegmentSignal.Operations.AtIdx
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import CORALean.Specification.PointSegmentSignal.Operations.Combine
public import CORALean.Specification.PointSegmentSignal.Operations.CombineLoop
public import CORALean.Specification.PointSegmentSignal.Operations.CutAtFirstFallingEdge
public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals
public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervalsBounds
public import CORALean.Specification.PointSegmentSignal.Operations.FindLast
public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.PointSegmentSignal.Operations.IndicatorBounds
public import CORALean.Specification.PointSegmentSignal.Operations.IntervalUntil
public import CORALean.Specification.PointSegmentSignal.Operations.IntervalUntilFloat
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStart
public import CORALean.Specification.PointSegmentSignal.Operations.RelevantStop
public import CORALean.Specification.PointSegmentSignal.Operations.Set
public import CORALean.Specification.PointSegmentSignal.Operations.SetPoint
public import CORALean.Specification.PointSegmentSignal.Operations.SuccTimeAtValIdx
public import CORALean.Specification.PointSegmentSignal.Operations.TimeOrInf
public import CORALean.Specification.PointSegmentSignal.Operations.Until
public import CORALean.Specification.PointSegmentSignal.Operations.UntilFloat

/-!
# Piecewise-constant signals, operations

The methods of `pointSegmentSignal`: `at`, `not`, `indicator`, `combine`, `set`, `anyTrue`,
`allTrue` and the accessors of its time points.
-/
