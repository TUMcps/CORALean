# contDynamics/@contDynamics

CORA methods of `contDynamics/@contDynamics/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Reach`, `OutputEq`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `conform` | out-of-scope | n/a — solver-dependent | dispatch to conformance synthesis by optimisation (`fmincon`/`linprog`) or RRT |
| `contDynamics` | out-of-scope | n/a — matlab-runtime | abstract class constructor: stores only dimensions and a name, which are type indices in Lean |
| `createTestSuite` | out-of-scope | n/a — random/sampling |  |
| `derivatives` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `isconform` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `linReach` | float | [`NonlinearSys.linReachPoly`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachPoly.lean), [`NonlinearSys.Trajectory.linReachPoly_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachPolyOuter.lean) · float: [`NonlinearSys.FloatHessModel.linReachFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachFloat.lean), [`NonlinearSys.FloatHessModel.Encloses.linReachFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachFloatOuter.lean) | route a; cora-issue — the check `R([iΔt,(i+1)Δt]) ⊆ R_i` is made on a set computed under the very confinement it checks, so it establishes nothing; CORALean takes confinement from an a priori ball about the step's start ([FINDINGS](../../../FINDINGS.md), "Confinement of a run to a linearization's region") |
| `linReachInner` | — | — |  |
| `observe` | proved | [`LinearSysDT.observeStripBased`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStripBased.lean), [`LinearSysDT.observeStripBased_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObserveStripBasedOuter.lean) | for `linearSysDT` at the strip-based estimators `FRad-A`, `FRad-B`, `PRad-A` to `PRad-D` and `VolMin-A`, which run `observe_stripBased`; the other estimators (`VolMin-B`, `FRad-C`, `PRad-E`, `Nom-G`, `Hinf-G`, `ESO-*`, `CZN-*`, `ROPO`) and `nonlinearSysDT` are not covered |
| `observe_stripBased` | proved | [`LinearSysDT.observeStripBased`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStripBased.lean), [`LinearSysDT.observeStripBased_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObserveStripBasedOuter.lean), [`LinearSysDT.observeStep`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStep.lean), [`LinearSysDT.observeStep_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObserveStepOuter.lean) | outer, for `linearSysDT`: every run `x_(k+1) = A x_k + u_k + w_k`, `w_k ∈ W`, whose outputs meet the strips `\|C x_k - y_k\| ≤ σ` is in the observer's set at every step; both intersection types (1, strips one at a time, `Zonotope.intersectStripSeq`; 2, all at once, `Zonotope.intersectStrip`) at every gain, fixed or computed from the zonotope being met, so the estimators `FRad-A`, `FRad-B`, `PRad-A` to `PRad-D` and `VolMin-A`; `σ` is CORA's `supremum(abs(interval(V)))`, taken as given; `'bravo'` (`VolMin-B`) and `nonlinearSysDT` are not covered |
| `outputSet` | float | [`OutputEq.outputSet`](../../../src/CORALean/ContDynamics/OutputEq/Operations/OutputSet.lean), [`OutputEq.outputSet_outer`](../../../src/CORALean/ContDynamics/OutputEq/Theorems/OutputSetOuter.lean) | route b — generic over `Scalar 𝕋` and the set operation classes, computable; run at `Dyadic` in `Examples/ReachFloat.lean` |
| `printSystem` | out-of-scope | n/a — plotting/display |  |
| `reach` | float | [`Reach`](../../../src/CORALean/ContDynamics/Reach/Reach.lean) | route b — the interface class is generic over the system and the representation; `LinearSysDT 𝕋` instantiates it at any scalar (`ContDynamics/LinearSysDT/Instances.lean`) |
| `simulateRandom` | out-of-scope | n/a — random/sampling |  |
| `symVariables` | out-of-scope | n/a — matlab-runtime |  |
| `verify` | float | [`Reach.holds_of_check`](../../../src/CORALean/ContDynamics/Reach/Theorems/HoldsOfCheck.lean), [`Reach.check`](../../../src/CORALean/ContDynamics/Reach/Operations/Check.lean), [`Reach`](../../../src/CORALean/ContDynamics/Reach/Reach.lean) | route b — generic over the system class and the representation; a `true` from `Reach.check` (the specification checked on `reach`) implies the specification on the exact reachable set, which is what CORA's `verify` returning true asserts; `false` and a failed `reach` prove nothing, as in CORA |
