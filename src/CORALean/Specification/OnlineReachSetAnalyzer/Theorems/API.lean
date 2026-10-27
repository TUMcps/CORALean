module

public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.Basic
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ForcePropagationFloatSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ForcePropagationSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.GetVerdictAp
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.GetVerdictConst
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.GetVerdictToRealAnalyzer
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.MkSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveSetErasedKeepsVerdict
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveSetSingleAp
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveSetSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ParseSpec
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.UpdateNodeSpec

/-!
# Online reach set analyzers, theorems

What the constructor builds, what an observation does, the verdict on the formulas `true`,
`false` and an atomic proposition, and an observation after which a less informed analyzer keeps a
verdict the exact one revises.
-/
