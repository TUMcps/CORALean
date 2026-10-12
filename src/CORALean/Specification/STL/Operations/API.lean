import CORALean.Specification.STL.Operations.BranchMerge
import CORALean.Specification.STL.Operations.CNFNext
import CORALean.Specification.STL.Operations.CNFOr
import CORALean.Specification.STL.Operations.CNFToFormula
import CORALean.Specification.STL.Operations.CNFUpsilon
import CORALean.Specification.STL.Operations.ClauseInsert
import CORALean.Specification.STL.Operations.ClauseMerge
import CORALean.Specification.STL.Operations.CompEval
import CORALean.Specification.STL.Operations.FormulaScale
import CORALean.Specification.STL.Operations.NnfToFormula
import CORALean.Specification.STL.Operations.NnfWeight
import CORALean.Specification.STL.Operations.RTLBigAnd
import CORALean.Specification.STL.Operations.RTLBigOr
import CORALean.Specification.STL.Operations.RTLFinally
import CORALean.Specification.STL.Operations.SampToCNF
import CORALean.Specification.STL.Operations.SampToFormula
import CORALean.Specification.STL.Operations.DFormulaBound
import CORALean.Specification.STL.Operations.EvaluatePredicateUnionCora
import CORALean.Specification.STL.Operations.EvaluatePredicateUnionPolytopeCora
import CORALean.Specification.STL.Operations.SafeToUnsafeCora
import CORALean.Specification.STL.Operations.VerifySTLKochdumperGloballyCora
import CORALean.Specification.STL.Operations.RobustnessReachSetGloballyCora
import CORALean.Specification.STL.Operations.AutomatedVerification
import CORALean.Specification.STL.Operations.FactorCheck
import CORALean.Specification.STL.Operations.FactorMeet
import CORALean.Specification.STL.Operations.FactorStep
import CORALean.Specification.STL.Operations.UnsafeFactors

/-!
# Signal and reachset temporal logic: the operations

Evaluating a composition `f(φ₁, …, φ_n)`, the STL formula a normal form stands for, and `Υ`
from sampled time STL to RTL. Beside them the verifier of Kochdumper and Bak: the unsafe factors
of a polytope, the model checking `factorCheck` that intersects them, and the loop
`automatedVerification` that halves the time step.
-/
