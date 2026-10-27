module

public import CORALean.Specification.OnlineReachSetAnalyzer.Counterexamples.API
public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.API
public import CORALean.Specification.OnlineReachSetAnalyzer.OnlineReachSetAnalyzer
public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.API
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.API

/-!
# Online reach set analyzers, collected

CORA's `onlineReachSetAnalyzer`: `OnlineReachSetAnalyzer` the data, `Definitions` the formula
it is made from and the state of its parser, `Operations` its methods, `Theorems` what each
computes and the verdict on small formulas, `Counterexamples` the run that shows
`observeSet_correct` needs its observation intervals disjoint.
-/
