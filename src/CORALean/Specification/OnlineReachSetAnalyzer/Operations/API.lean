module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ForcePropagation
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ForcePropagationFloat
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.FormulaKey
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.FormulaKind
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.GetVerdict
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Mk
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ObserveSet
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Parse
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ParseNew
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Propagate
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.PropagateFloat
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.PropagateRec
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ToRealAnalyzer

/-!
# Online reach set analyzers, operations

The methods of `onlineReachSetAnalyzer`: the constructor, `observeSet`, `forcePropagation` and
`getVerdict`, and the private `parse`, `propagate` and `propagateRec` they are written from.
-/
