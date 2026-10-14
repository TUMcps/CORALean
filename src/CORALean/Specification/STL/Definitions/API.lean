module

public import CORALean.Specification.STL.Definitions.BranchHolds
public import CORALean.Specification.STL.Definitions.CDivisibleFormula
public import CORALean.Specification.STL.Definitions.Composition
public import CORALean.Specification.STL.Definitions.Halfspace
public import CORALean.Specification.STL.Definitions.Nnf
public import CORALean.Specification.STL.Definitions.NnfRewrite
public import CORALean.Specification.STL.Definitions.Pform
public import CORALean.Specification.STL.Definitions.RTL
public import CORALean.Specification.STL.Definitions.ReachSequence
public import CORALean.Specification.STL.Definitions.Samp
public import CORALean.Specification.STL.Definitions.SampledTime
public import CORALean.Specification.STL.Definitions.Shift
public import CORALean.Specification.STL.Definitions.Transformation
public import CORALean.Specification.STL.Definitions.DiscreteFormula
public import CORALean.Specification.STL.Definitions.MILPEncoding
public import CORALean.Specification.STL.Definitions.Tsupp
public import CORALean.Specification.STL.Definitions.MilpCorrected
public import CORALean.Specification.STL.Definitions.MilpPrinted
public import CORALean.Specification.STL.Definitions.DepReachConsts
public import CORALean.Specification.STL.Definitions.DepReachState
public import CORALean.Specification.STL.Definitions.DependencyPreservedBy
public import CORALean.Specification.STL.Definitions.VerificationProblem
public import CORALean.Specification.STL.Definitions.Cmp
public import CORALean.Specification.STL.Definitions.Expr
public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Definitions.TreeWellFormed

/-!
# Signal and reachset temporal logic: the definitions

Propositional formulas, RTL, reach sequences and what makes a transformation between the logics
sound and complete, and the normal form `Υ` is defined on; STL itself is `STL.lean`.
`DiscreteFormula` is STL over discrete time with its robustness, and `MILPEncoding` the values
its mixed-integer encodings force. `MilpPrinted` and `MilpCorrected` are the program (26) of
Kochdumper and Bak's automated verifier, as printed and with its strict inequality repaired.
`DepReachConsts` and `DepReachState` are what its Alg. 1 carries, `DependencyPreservedBy` its
Def. 4, `VerificationProblem` its Sec. 3.
-/
