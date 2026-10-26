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
public import CORALean.Specification.STL.Operations.DFormulaRob
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
public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.CmpDual
public import CORALean.Specification.STL.Operations.CmpNegate
public import CORALean.Specification.STL.Operations.TreeAssignIdentifiersFrom
public import CORALean.Specification.STL.Operations.TreeCnfLoop
public import CORALean.Specification.STL.Operations.TreeCnfRewrite
public import CORALean.Specification.STL.Operations.TreeCombineNext
public import CORALean.Specification.STL.Operations.TreeCompare
public import CORALean.Specification.STL.Operations.TreeConjoin
public import CORALean.Specification.STL.Operations.TreeConjunctiveNormalForm
public import CORALean.Specification.STL.Operations.TreeDesugar
public import CORALean.Specification.STL.Operations.TreeDisjunctiveNormalForm
public import CORALean.Specification.STL.Operations.TreeDnfLoop
public import CORALean.Specification.STL.Operations.TreeDnfRewrite
public import CORALean.Specification.STL.Operations.TreeEliminateTrueFalseWith
public import CORALean.Specification.STL.Operations.TreeGetVariables
public import CORALean.Specification.STL.Operations.TreeHalfspace2set
public import CORALean.Specification.STL.Operations.TreeIsLinearPredicate
public import CORALean.Specification.STL.Operations.TreeMaximumTimeFrom
public import CORALean.Specification.STL.Operations.TreeMinimumTimeFrom
public import CORALean.Specification.STL.Operations.TreeNnfWith
public import CORALean.Specification.STL.Operations.TreePolytope2stl
public import CORALean.Specification.STL.Operations.TreeTemporal
public import CORALean.Specification.STL.Operations.ExprIsLinear
public import CORALean.Specification.STL.Operations.ExprVariables
public import CORALean.Specification.STL.Operations.DepBloatingFloat
public import CORALean.Specification.STL.Operations.DepBoxFloat
public import CORALean.Specification.STL.Operations.DepCurvatureFFloat
public import CORALean.Specification.STL.Operations.DepCurvatureGFloat
public import CORALean.Specification.STL.Operations.DepReachAtFloat
public import CORALean.Specification.STL.Operations.DepReachConstsOfFloat
public import CORALean.Specification.STL.Operations.DepReachFloat
public import CORALean.Specification.STL.Operations.DepReachInitFloat
public import CORALean.Specification.STL.Operations.DepReachIntervalFloat
public import CORALean.Specification.STL.Operations.DepReachPointFloat
public import CORALean.Specification.STL.Operations.DepReachStepFloat

/-!
# Signal and reachset temporal logic: the operations

Evaluating a composition `f(φ₁, …, φ_n)`, the STL formula a normal form stands for, and `Υ`
from sampled time STL to RTL. Beside them the verifier of Kochdumper and Bak: the unsafe factors
of a polytope, the model checking `factorCheck` that intersects them, and the loop
`automatedVerification` that halves the time step, and its dependency preserving reachability
analysis `depReach` (Alg. 1) with the sets of Eqs. (14)-(20).
-/
