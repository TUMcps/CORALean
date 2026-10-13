module

public import CORALean.Specification.STL.Operations.BranchMerge
public import CORALean.Specification.STL.Operations.CNFNext
public import CORALean.Specification.STL.Operations.CNFOr
public import CORALean.Specification.STL.Operations.CNFToFormula
public import CORALean.Specification.STL.Operations.CNFUpsilon
public import CORALean.Specification.STL.Operations.ClauseInsert
public import CORALean.Specification.STL.Operations.ClauseMerge
public import CORALean.Specification.STL.Operations.CompEval
public import CORALean.Specification.STL.Operations.FormulaScale
public import CORALean.Specification.STL.Operations.NnfToFormula
public import CORALean.Specification.STL.Operations.NnfWeight
public import CORALean.Specification.STL.Operations.RTLBigAnd
public import CORALean.Specification.STL.Operations.RTLBigOr
public import CORALean.Specification.STL.Operations.RTLFinally
public import CORALean.Specification.STL.Operations.SampToCNF
public import CORALean.Specification.STL.Operations.SampToFormula
public import CORALean.Specification.STL.Operations.DFormulaBound
public import CORALean.Specification.STL.Operations.EvaluatePredicateUnionCora
public import CORALean.Specification.STL.Operations.EvaluatePredicateUnionPolytopeCora
public import CORALean.Specification.STL.Operations.SafeToUnsafeCora
public import CORALean.Specification.STL.Operations.VerifySTLKochdumperGloballyCora
public import CORALean.Specification.STL.Operations.RobustnessReachSetGloballyCora
public import CORALean.Specification.STL.Operations.AutomatedVerification
public import CORALean.Specification.STL.Operations.FactorCheck
public import CORALean.Specification.STL.Operations.FactorMeet
public import CORALean.Specification.STL.Operations.FactorStep
public import CORALean.Specification.STL.Operations.UnsafeFactors
public import CORALean.Specification.STL.Operations.DepCurvatureF
public import CORALean.Specification.STL.Operations.DepCurvatureG
public import CORALean.Specification.STL.Operations.DepBloating
public import CORALean.Specification.STL.Operations.DepBox
public import CORALean.Specification.STL.Operations.DepReachConstsOf
public import CORALean.Specification.STL.Operations.DepReachInit
public import CORALean.Specification.STL.Operations.DepReachStep
public import CORALean.Specification.STL.Operations.DepReachAt
public import CORALean.Specification.STL.Operations.DepReachPoint
public import CORALean.Specification.STL.Operations.DepReachInterval
public import CORALean.Specification.STL.Operations.DepReach

/-!
# Signal and reachset temporal logic: the operations

Evaluating a composition `f(φ₁, …, φ_n)`, the STL formula a normal form stands for, and `Υ`
from sampled time STL to RTL. Beside them the verifier of Kochdumper and Bak: the unsafe factors
of a polytope, the model checking `factorCheck` that intersects them, and the loop
`automatedVerification` that halves the time step, and its dependency preserving reachability
analysis `depReach` (Alg. 1) with the sets of Eqs. (14)-(20).
-/
