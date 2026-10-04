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

/-!
# Signal and reachset temporal logic: the operations

Evaluating a composition `f(φ₁, …, φ_n)`, the STL formula a normal form stands for, and `Υ`
from sampled time STL to RTL.
-/
