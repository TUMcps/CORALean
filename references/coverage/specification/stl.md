# specification/@stl

CORA methods of `specification/@stl/` (a class of `specification/` or `specification/signals/`; a single-file class lists its public methods, constructor included), one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `STL.Formula` (`src/CORALean/Specification/STL/`), the syntax and semantics of signal temporal logic over traces `ℝ≥0 → X`, with the model-checking pipeline of [Roehm et al.](../../2016/roehm-atva-stl-model-checking.md) (negation normal form, sampled time, CNF, `Υ`) and the verification loop of [Kochdumper and Bak](../../2024/kochdumper-nahs-stl-lti-verification.md). Those follow the papers' algorithms, not CORA's methods one by one, so a method is `proved` here only where a theorem is about what the method builds.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `and` | proved | [`STL.Formula.sat_and`](../../../src/CORALean/Specification/STL/Theorems/SatAnd.lean) | the denotation of the connective, `STL.Formula.and` (De Morgan of `not` and `or`): satisfied iff both operands are; CORA's `and` builds a syntax-tree node and evaluates nothing, so this is the semantics the node is read with |
| `assignIdentifiers` | — | — |  |
| `combineAtomicPropositions` | — | — |  |
| `combineNext` | — | — |  |
| `conjunctiveNormalForm` | — | — |  |
| `consistentTimeStep` | — | — |  |
| `convert2set` | — | — |  |
| `desugar` | — | — |  |
| `disjunctiveNormalForm` | — | — |  |
| `disp` | out-of-scope | n/a — plotting/display |  |
| `eliminateTrueFalse` | — | — |  |
| `evalPredicates` | — | — |  |
| `evaluateSignal` | — | — |  |
| `finally` | — | — | definition only, no theorem: [`STL.Formula.finally`](../../../src/CORALean/Specification/STL/STL.lean) is `true U[a,b] φ` |
| `ge` | — | — |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getClauses` | — | — |  |
| `getTimes` | — | — |  |
| `getVariables` | — | — |  |
| `globally` | — | — |  |
| `gradientRobustness` | — | — |  |
| `gt` | — | — |  |
| `implies` | — | — |  |
| `in` | — | — |  |
| `isLinearPredicate` | — | — |  |
| `isPredicate` | — | — |  |
| `isequal` | out-of-scope | n/a — matlab-runtime | compares MATLAB objects field by field |
| `le` | — | — |  |
| `lt` | — | — |  |
| `masks` | — | — |  |
| `maximumTime` | — | — |  |
| `minimumTime` | — | — |  |
| `minus` | — | — |  |
| `modelCheckReachSet` | — | — |  |
| `modelCheckTrace` | — | — |  |
| `negationNormalForm` | — | — |  |
| `next` | proved | [`STL.Formula.sat_next`](../../../src/CORALean/Specification/STL/Theorems/SatNext.lean) | `STL.Formula.next a φ`, `true U[a,a] φ`: satisfied iff `φ` holds on the trace shifted by `a`; CORA's `next(obj,time)` builds a syntax-tree node |
| `nonlinearOperator` | — | — |  |
| `not` | — | — |  |
| `or` | proved | [`STL.Formula.sat_or`](../../../src/CORALean/Specification/STL/Theorems/SatOr.lean) | the denotation of the connective, `STL.Formula.or`: satisfied iff one operand is; CORA's `or` builds a syntax-tree node and evaluates nothing, so this is the semantics the node is read with |
| `plus` | — | — |  |
| `polytope2stl` | — | — |  |
| `power` | — | — |  |
| `release` | proved | [`STL.Formula.sat_release`](../../../src/CORALean/Specification/STL/Theorems/SatRelease.lean) | `STL.Formula.release a b φ ψ`, the dual `¬(¬φ U[a,b] ¬ψ)`: at every `t ∈ [a,b]` either `ψ` holds or `φ` held strictly earlier; CORA's `release(obj1,obj2,time)` builds a syntax-tree node |
| `robustness` | — | — | definition only, no theorem: [`STL.robustnessReachSetGloballyCora`](../../../src/CORALean/Specification/STL/Operations/RobustnessReachSetGloballyCora.lean) models `aux_robustnessReachSet` as printed on one path (one branch, one state, `globally(x(1) > 0, ...)`), not the general method; cora-issue — on the reach-set branch with several sets per window, `aux_robustnessReachSet` (l. 292-297) overwrites `r(j,i)` instead of taking the minimum, so a window carries the last set's robustness and a violation in an earlier set is missed ([`STL.robustnessReachSetGloballyCora_lastSetOnly_counterexample`](../../../src/CORALean/Specification/STL/Theorems/RobustnessReachSetLastSetOnlyCounterexample.lean); [FINDINGS](../../../FINDINGS.md), "`stl/robustness` on a reach set, window over several sets") |
| `robustnessEncodingMILP` | out-of-scope | n/a — solver-dependent | MILP encoding for an external solver |
| `sampledTime` | — | — |  |
| `stl` | — | — | definition only, no theorem: [`STL.Formula`](../../../src/CORALean/Specification/STL/STL.lean) is the syntax and `STL.Formula.Sat` the semantics of [Roehm et al.](../../2016/roehm-atva-stl-model-checking.md); CORA's `stl` is a syntax tree over named variables, here a formula over any state type |
| `stl2rtl` | — | — |  |
| `subsref` | out-of-scope | n/a — matlab-runtime |  |
| `times` | — | — |  |
| `until` | — | — | definition only, no theorem: [`STL.Formula.Sat`](../../../src/CORALean/Specification/STL/STL.lean) gives the `until` clause of the semantics |
