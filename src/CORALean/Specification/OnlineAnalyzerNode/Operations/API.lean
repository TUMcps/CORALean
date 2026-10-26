module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.ApValue
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Basic
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Combine
public import CORALean.Specification.OnlineAnalyzerNode.Operations.CombineFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Conflicts
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ConflictsFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.GetAllProp
public import CORALean.Specification.OnlineAnalyzerNode.Operations.GetAllPropFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Mk
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ObserveSet
public import CORALean.Specification.OnlineAnalyzerNode.Operations.PropBound
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Propagate
public import CORALean.Specification.OnlineAnalyzerNode.Operations.PropagateFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.SetPropagated
public import CORALean.Specification.OnlineAnalyzerNode.Operations.SetPropagatedFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ToRealNode

/-!
# Online analyzer nodes, operations

The methods of `onlineAnalyzerNode`: the constructor, `observeSet`, `setPropagated` and
`propagate`, and the private `getAllProp` and `combine` they use, and `apValue` and `conflicts`,
the two steps of `observeSet`.
-/
