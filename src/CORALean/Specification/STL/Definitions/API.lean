import CORALean.Specification.STL.Definitions.BranchHolds
import CORALean.Specification.STL.Definitions.CDivisibleFormula
import CORALean.Specification.STL.Definitions.Composition
import CORALean.Specification.STL.Definitions.Halfspace
import CORALean.Specification.STL.Definitions.Nnf
import CORALean.Specification.STL.Definitions.NnfRewrite
import CORALean.Specification.STL.Definitions.Pform
import CORALean.Specification.STL.Definitions.RTL
import CORALean.Specification.STL.Definitions.ReachSequence
import CORALean.Specification.STL.Definitions.Samp
import CORALean.Specification.STL.Definitions.SampledTime
import CORALean.Specification.STL.Definitions.Shift
import CORALean.Specification.STL.Definitions.Transformation
import CORALean.Specification.STL.Definitions.DiscreteFormula
import CORALean.Specification.STL.Definitions.MILPEncoding
import CORALean.Specification.STL.Definitions.Tsupp

/-!
# Signal and reachset temporal logic: the definitions

Propositional formulas, RTL, reach sequences and what makes a transformation between the logics
sound and complete, and the normal form `Υ` is defined on; STL itself is `STL.lean`.
`DiscreteFormula` is STL over discrete time with its robustness, and `MILPEncoding` the values
its mixed-integer encodings force.
-/
