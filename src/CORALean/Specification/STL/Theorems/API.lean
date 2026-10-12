import CORALean.Specification.STL.Theorems.BlocksDisjoint
import CORALean.Specification.STL.Theorems.BranchHoldsMerge
import CORALean.Specification.STL.Theorems.BranchHoldsShift
import CORALean.Specification.STL.Theorems.CNFSatAppend
import CORALean.Specification.STL.Theorems.CNFSatNext
import CORALean.Specification.STL.Theorems.CNFSatOr
import CORALean.Specification.STL.Theorems.CNFSatToFormula
import CORALean.Specification.STL.Theorems.CNFSatUpsilon
import CORALean.Specification.STL.Theorems.CNFUpsilonDuplicateCounterexample
import CORALean.Specification.STL.Theorems.CNFUpsilonEmptyCounterexample
import CORALean.Specification.STL.Theorems.CNFUpsilonSoundComplete
import CORALean.Specification.STL.Theorems.ClauseHoldsInsert
import CORALean.Specification.STL.Theorems.ClauseHoldsMerge
import CORALean.Specification.STL.Theorems.ClauseNodupInsert
import CORALean.Specification.STL.Theorems.ClauseNodupMerge
import CORALean.Specification.STL.Theorems.CompSound
import CORALean.Specification.STL.Theorems.ExistsNnf
import CORALean.Specification.STL.Theorems.EvaluatePredicateUnionLastOnlyCounterexample
import CORALean.Specification.STL.Theorems.FinOpenNextEquiv
import CORALean.Specification.STL.Theorems.FinRepConstOnBlock
import CORALean.Specification.STL.Theorems.FinallyAIff
import CORALean.Specification.STL.Theorems.ForallExistsIffExistsForall
import CORALean.Specification.STL.Theorems.ForallFinalsOrGlobalsIff
import CORALean.Specification.STL.Theorems.ForallLtAddOneOfBlocks
import CORALean.Specification.STL.Theorems.ForallLtTwoOfBlocks
import CORALean.Specification.STL.Theorems.ForallTraceSetSatIff
import CORALean.Specification.STL.Theorems.GlobOpenNextEquiv
import CORALean.Specification.STL.Theorems.ModelCheckingComplete
import CORALean.Specification.STL.Theorems.ModelCheckingSound
import CORALean.Specification.STL.Theorems.NextAIffSubsetIUnion
import CORALean.Specification.STL.Theorems.NnfExistsSampled
import CORALean.Specification.STL.Theorems.NnfRewriteAnd
import CORALean.Specification.STL.Theorems.NnfRewriteLit
import CORALean.Specification.STL.Theorems.NnfRewriteOr
import CORALean.Specification.STL.Theorems.NnfRewriteRelease
import CORALean.Specification.STL.Theorems.NnfRewriteUntil
import CORALean.Specification.STL.Theorems.PformExistsDnf
import CORALean.Specification.STL.Theorems.PformSatBigOr
import CORALean.Specification.STL.Theorems.RTLSatBigAnd
import CORALean.Specification.STL.Theorems.RTLSatBigOr
import CORALean.Specification.STL.Theorems.ReleaseZeroEquiv
import CORALean.Specification.STL.Theorems.RewriteFinOpenAnd
import CORALean.Specification.STL.Theorems.RewriteFinOpenOr
import CORALean.Specification.STL.Theorems.RewriteFinOpenReleaseSucc
import CORALean.Specification.STL.Theorems.RewriteFinOpenReleaseZero
import CORALean.Specification.STL.Theorems.RewriteFinOpenUntilSucc
import CORALean.Specification.STL.Theorems.RewriteFinOpenUntilZero
import CORALean.Specification.STL.Theorems.RewriteGlobOpenAnd
import CORALean.Specification.STL.Theorems.RewriteGlobOpenOr
import CORALean.Specification.STL.Theorems.RewriteGlobOpenReleaseSucc
import CORALean.Specification.STL.Theorems.RewriteGlobOpenReleaseZero
import CORALean.Specification.STL.Theorems.RewriteGlobOpenUntilSucc
import CORALean.Specification.STL.Theorems.RewriteGlobOpenUntilZero
import CORALean.Specification.STL.Theorems.RewriteReleaseSucc
import CORALean.Specification.STL.Theorems.RewriteReleaseZero
import CORALean.Specification.STL.Theorems.RewriteUntilSucc
import CORALean.Specification.STL.Theorems.RewriteUntilZero
import CORALean.Specification.STL.Theorems.STLSatBigAnd
import CORALean.Specification.STL.Theorems.STLSatBigOr
import CORALean.Specification.STL.Theorems.SampNodupToCNF
import CORALean.Specification.STL.Theorems.SampSatToCNF
import CORALean.Specification.STL.Theorems.SampToFormulaScale
import CORALean.Specification.STL.Theorems.SatAnd
import CORALean.Specification.STL.Theorems.SatNext
import CORALean.Specification.STL.Theorems.SatOfPform
import CORALean.Specification.STL.Theorems.SatOr
import CORALean.Specification.STL.Theorems.SatRelease
import CORALean.Specification.STL.Theorems.SatScale
import CORALean.Specification.STL.Theorems.SatTt
import CORALean.Specification.STL.Theorems.ScaleOfPform
import CORALean.Specification.STL.Theorems.ShiftShift
import CORALean.Specification.STL.Theorems.ShiftZero
import CORALean.Specification.STL.Theorems.TraceSetExactCounterexample
import CORALean.Specification.STL.Theorems.TracesSubsetTraceSet
import CORALean.Specification.STL.Theorems.UntilZeroEquiv
import CORALean.Specification.STL.Theorems.UpsilonAnd
import CORALean.Specification.STL.Theorems.UpsilonOfPform
import CORALean.Specification.STL.Theorems.UpsilonOfPformCounterexample
import CORALean.Specification.STL.Theorems.UntilEncNonstrictIff
import CORALean.Specification.STL.Theorems.UntilDecompIff
import CORALean.Specification.STL.Theorems.UntilRobNonstrictLeIff
import CORALean.Specification.STL.Theorems.ZEncIffSat
import CORALean.Specification.STL.Theorems.REncEqRob
import CORALean.Specification.STL.Theorems.ZEncCounterexample
import CORALean.Specification.STL.Theorems.REncCounterexample
import CORALean.Specification.STL.Theorems.RobSound
import CORALean.Specification.STL.Theorems.RobCounterexample
import CORALean.Specification.STL.Theorems.SatCongr
import CORALean.Specification.STL.Theorems.EventuallySatIff
import CORALean.Specification.STL.Theorems.PredEncodingIff
import CORALean.Specification.STL.Theorems.ConjEncodingIff
import CORALean.Specification.STL.Theorems.DisjEncodingIff
import CORALean.Specification.STL.Theorems.RobustConjEncoding
import CORALean.Specification.STL.Theorems.RobustDisjEncoding
import CORALean.Specification.STL.Theorems.RobustSelectorCounterexample
import CORALean.Specification.STL.Theorems.TsuppSubsetOfDecided
import CORALean.Specification.STL.Theorems.UpsilonOrOfDecided
import CORALean.Specification.STL.Theorems.UpsilonOrCounterexample
import CORALean.Specification.STL.Theorems.AutomatedVerificationSound
import CORALean.Specification.STL.Theorems.FactorCheckSound
import CORALean.Specification.STL.Theorems.FactorMeetZipCounterexample
import CORALean.Specification.STL.Theorems.FactorStepMem
import CORALean.Specification.STL.Theorems.MilpCorrectedIff
import CORALean.Specification.STL.Theorems.MilpPrintedCounterexample
import CORALean.Specification.STL.Theorems.MilpPrintedInfeasible
import CORALean.Specification.STL.Theorems.NotMemOfNotMemUnsafeFactors

/-!
# Signal and reachset temporal logic: the theorems

The results of [1] that are formalized, one file each: the properties of a sound and complete
transformation, its soundness and completeness on c-divisible reach sequences ([1, Lemma 2]), the
rewriting rules of [1, Table 1], and the lemmas about traces and sets they use. The `aux_` lemmas
are re-exported too. Beside them, the mixed-integer encodings of discrete-time STL: each
constraint gadget, and the encodings deciding the formula and computing its robustness. Of [2]:
the unsafe factors of a polytope, the soundness of the model checking over them and of the
automated verifier built on it, and the program (26) of its falsification, infeasible as printed.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
* [2] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/
