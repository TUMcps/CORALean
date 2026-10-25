module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.IsBranch
public import CORALean.Specification.ReachSetAnalyzer.Definitions.Entry
public import CORALean.Specification.ReachSetAnalyzer.Definitions.IsFalseMark
public import CORALean.Specification.ReachSetAnalyzer.Definitions.HasEnclosingTimes
public import CORALean.Specification.ReachSetAnalyzer.Definitions.Represents
public import CORALean.Specification.ReachSetAnalyzer.Definitions.SignalsSound
public import CORALean.Specification.ReachSetAnalyzer.Definitions.TimedSet
public import CORALean.Specification.ReachSetAnalyzer.Definitions.IsTrueMark

/-!
# Reach set analyzers, definitions

The part of a `reachSet` the analyzer reads, the branches of the tree of reach sets, what an
analyzer says, what marks a time as possibly true or possibly false, and when signals are sound for
a branch.
-/
