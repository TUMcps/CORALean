# contDynamics/@contDynamics

CORA methods of `contDynamics/@contDynamics/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `ContDynamics` and `ContDynamicsDT` (the dimensions and what a run is, instantiated by every system class but `LinProbSys`), `Reach`, `OutputEq`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `conform` | out-of-scope | n/a — solver-dependent | dispatch to conformance synthesis by optimisation (`fmincon`/`linprog`) or RRT |
| `contDynamics` | out-of-scope | n/a — matlab-runtime | abstract class constructor: stores only dimensions and a name; the dimensions are `ContDynamics`'s `n`, `nrOfInputs` and `nrOfDisturbances`, the name has no counterpart |
| `createTestSuite` | out-of-scope | n/a — random/sampling |  |
| `derivatives` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `isconform` | bound | [`Conform.PassesBF`](../../../src/CORALean/ContDynamics/Conform/Definitions/PassesBF.lean), [`Conform.passesBF_of_isConformant`](../../../src/CORALean/ContDynamics/Conform/Theorems/PassesBFOfConformant.lean), [`Conform.Plant.IsConformant`](../../../src/CORALean/ContDynamics/Conform/Definitions/IsConformant.lean), [`Conform.Plant.isConformant_iff_lp`](../../../src/CORALean/ContDynamics/Conform/Theorems/ConformantIffLp.lean), [`LinearSysDT.IsConformDyn`](../../../src/CORALean/ContDynamics/LinearSysDT/Definitions/IsConformDyn.lean), [`LinearSysDT.isConformDyn_of_model`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/IsConformDynOfModel.lean) | specification, CORA: the verdict of an algorithm that computes the reach sets itself; here a Prop, `PassesBF`, with the sets `R` a parameter, and only one direction proved (a conformant system passes, so a measurement outside a computed set proves non-conformance). partial: the deterministic branches. Real layer, a specification over ℝ. Details below. |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `linReach` | float | [`NonlinearSys.linReachPoly`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachPoly.lean), [`NonlinearSys.IsTrajectory.linReachPoly_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachPolyOuter.lean) · float: [`NonlinearSys.FloatHessModel.linReachFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachFloat.lean), [`NonlinearSys.FloatHessModel.Encloses.linReachFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachFloatOuter.lean) | route a; cora-issue — CORA's `linReach` bounds the Lagrange remainder over `interval(Rmax) + p` only, which can miss the segment from the linearization point `p`, and its third-order tensor branches index the wrong tensor or factor ([`NonlinearSys.linReachCora1D`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachCora1D.lean), [`NonlinearSys.linReachCora1D_hessianRegion_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachCora1D.lean), [`NonlinearSys.linReachAdaptiveCora1D_hessianRegion_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachAdaptiveCora1D.lean), [`NonlinearSys.IsTrajectory.confined_of_ball`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ConfinedOfBall.lean), [`NonlinearSys.IsTrajectory.confinement_of_subset`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ConfinementOfSubset.lean)) ([`NonlinearSys.linReachTensor3Cora2D_index_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachTensor3Cora2D.lean), [`NonlinearSys.linReachTensor3Cora2D`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachTensor3Cora2D.lean), [`NonlinearSys.abstrErrAdaptiveTensor3Cora2D_factor_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/AbstrErrAdaptiveTensor3Cora2D.lean)). Details below. |
| `linReachInner` | proved | [`NonlinearSys.linReachInner`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachInner.lean), [`NonlinearSys.aux_linReachInnerErr`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachInner.lean), [`NonlinearSys.LinReachInnerOps`](../../../src/CORALean/ContDynamics/NonlinearSys/Definitions/LinReachInnerOps.lean), [`NonlinearSys.linReachInner_subset_reachSetExact`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachInnerSubsetReachSetExact.lean), [`NonlinearSys.linReachInner_Rti_subset_reachSetExact`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachInnerRtiSubsetReachSetExact.lean), [`NonlinearSys.IsLinReachInnerCert`](../../../src/CORALean/ContDynamics/NonlinearSys/Definitions/IsLinReachInnerCert.lean), [`NonlinearSys.IsLinReachInnerCert.of_abstractionError`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachInnerCertOfAbstractionError.lean) | cora-issue — CORA's `@contDynamics/linReachInner.m` returns as `Rti` the hull of (23) of Wetzlinger-Kulmburg-Althoff L-CSS 2024, `Prop. 2`, which is false even for convex start sets, and takes the Minkowski difference of its zonotopes by an unsound default; Formalized: the counterexample against (23) ([`convexHull_timeInterval_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeInterval.lean), [`convexHull_timeInterval_convex_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeIntervalConvex.lean), [`Zonotope.minkDiffApprox_not_inner`](../../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffApproxNotInner.lean), [`NonlinearSys.minkowskiDiff_inputSolution_subset_reachSetExact`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffInputSolutionSubsetReachSetExact.lean), [`NonlinearSys.reachInnerMinkdiff_subset_reachSetExact`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachInnerMinkdiffSubsetReachSetExact.lean), [`Zonotope.minkDiffApprox`](../../../src/CORALean/ContSet/Zonotope/Real/Operations/MinkDiffApprox.lean)). Details below. |
| `observe` | float | [`LinearSysDT.observeStripBased`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStripBased.lean), [`LinearSysDT.observeStripBased_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ObserveStripBasedOuter.lean), [`LinearSysDT.observePropagation`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObservePropagation.lean), [`LinearSysDT.observePropagation_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObservePropagationOuter.lean), [`LinearSysDT.observeInterval`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveInterval.lean), [`LinearSysDT.observeInterval_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObserveIntervalOuter.lean) · float: [`LinearSysDT.observePropagationFloat`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObservePropagationFloat.lean), [`LinearSysDT.observeIntervalFloat`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveIntervalFloat.lean), [`LinearSysDT.observePropagationFloat_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ObservePropagationFloatOuter.lean), [`LinearSysDT.observeIntervalFloat_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ObserveIntervalFloatOuter.lean) | Covered: the strip-based estimators `FRad-A`, `FRad-B`, `PRad-A` to `PRad-D` and `VolMin-A` (`observe_stripBased`), the set-propagation estimators `FRad-C`, `PRad-E` and `Nom-G` at every gain (`observePropagation`), all for `linearSysDT`; `VolMin-B`, `ESO-*`, `CZN-*`, `ROPO` and `nonlinearSysDT` are not covered. Every observer reads `A`, `B`, `C` off the system, and the strip-based and ellipsoidal ones also `c`, as CORA's `post` adds it; the gain `L` (`options.L`, or the gain function) is an argument, as in CORA. cora-issue — CORA's `priv_observe_interval.m` starts its error set at `R0` instead of `R0 - center(R0)`, and `observe` ignores `params.U`, the output offset, the state offset and an `E` or `F` other than the identity; the counterexample theorems are in the [`linearSysDT` `executeObserver`](linearSysDT.md) row. Details below. |
| `observe_stripBased` | float | [`LinearSysDT.observeStripBased`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStripBased.lean), [`LinearSysDT.observeStripBased_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ObserveStripBasedOuter.lean), [`LinearSysDT.observeStep`](../../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveStep.lean), [`LinearSysDT.observeStep_outer`](../../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ObserveStepOuter.lean), [`ContSet.intersectStripSeq`](../../../src/CORALean/ContSet/ContSet/Operations/IntersectStripSeq.lean), [`ContSet.intersectStripSeq_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/IntersectStripSeqOuter.lean), [`IntersectStrip`](../../../src/CORALean/ContSet/ContSet/Interfaces.lean) | route b — generic over `Scalar 𝕋` and the set operation classes (`Plus`, `Mtimes`, `OfScalarPoint`, `Reduce`, `IntersectStrip`), computable; `Real.Zonotope` and `Float.Zonotope` both instantiate them, so one theorem is the soundness of the exact and the rounded observer. Outer, for `linearSysDT`: every run `x_(k+1) = A x_k + u_k + w_k`, `w_k ∈ W`, whose outputs meet the strips `\|C x_k - y_k\| ≤ σ` is in the observer's set at every step. Both intersection types (1, strips one at a time, `ContSet.intersectStripSeq`; 2, all at once, `intersectStrip`) at every gain, fixed or computed from the set being met, so the estimators `FRad-A`, `FRad-B`, `PRad-A` to `PRad-D` and `VolMin-A`. `σ` is CORA's `supremum(abs(interval(V)))`, taken as given; `'bravo'` (`VolMin-B`) and `nonlinearSysDT` are not covered |
| `outputSet` | float | [`OutputEq.outputSet`](../../../src/CORALean/ContDynamics/OutputEq/Operations/OutputSet.lean), [`OutputEq.outputSet_outer`](../../../src/CORALean/ContDynamics/OutputEq/Theorems/OutputSetOuter.lean) | route b — generic over `Scalar 𝕋` and the set operation classes, computable; run at `Dyadic` in `Examples/ReachFloat.lean`; cora-issue — CORA's `@contDynamics/outputSet.m` evaluates the output at inputs shifted by `-center(U)`, because `postProcessing` moves `center(U)` into `params.u` and `aux_outputSet` never reads `uTrans` ([`NonlinearSys.outputSetCora_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/OutputSetCora.lean)). Details below. |
| `printSystem` | out-of-scope | n/a — plotting/display |  |
| `reach` | float | [`Reach`](../../../src/CORALean/ContDynamics/Interfaces.lean) | route b — the interface class is generic over the system and the representation; `LinearSysDT 𝕋` instantiates it at any scalar (`ContDynamics/LinearSysDT/Instances.lean`); `reach` returns `none` where CORA raises an error (a run that cannot certify its soundness conditions), and `reach_outer` holds of a set only at `reach … = some R`, so a failed run is no enclosure of anything |
| `simulateRandom` | out-of-scope | n/a — random/sampling |  |
| `symVariables` | out-of-scope | n/a — matlab-runtime |  |
| `verify` | float | [`Reach.holds_of_check`](../../../src/CORALean/ContDynamics/Reach/Theorems/HoldsOfCheck.lean), [`Reach.check`](../../../src/CORALean/ContDynamics/Reach/Operations/Check.lean), [`Reach`](../../../src/CORALean/ContDynamics/Interfaces.lean) | route b — generic over the system class and the representation; a `true` from `Reach.check` (the specification checked on `reach`) implies the specification on the exact reachable set, which is what CORA's `verify` returning true asserts; `false` and a failed `reach` prove nothing, as in CORA |

## Details

**`isconform` — the `BF` type.** `type = "BF"` (`priv_isconform_BF`) computes the reachable set of
every test case and requires each measurement up to the horizon in the set of its step. This is
`Conform.PassesBF`, with `passesBF_of_isConformant` saying a reachset-conformant system passes
whenever the sets enclose its reachable output sets, so a measurement outside a computed set proves
non-conformance. It is an outer statement: passing shows only containment in an enclosure, not
conformance, and the sets `R` are a parameter, whatever `reach` computes.

**`isconform` — the `dyn` type.** `type = "dyn"` is `isconform_dyn`, the halfspace containment of
the unified outputs, exact for the linear discrete-time plant (`linearSysDT` row `isconform_dyn`:
`Conform.Plant.isConformant_iff_lp`, `LinearSysDT.IsConformDyn`).

**`isconform` — the `RRT` type.** `type = "RRT"` (`priv_isconform_RRT`), a random tree search for a
violating trajectory, is not formalized, nor are the test-suite objects' file formats
(`params.testSuite`, `unifiedOutputs` as MATLAB structures).

**`linReach` — cora-issue, the Hessian region.** CORA's `linReach` checks `R([iΔt, (i+1)Δt]) ⊆ R_i`
after the fact — its `while perfIndCurr > 1` loop stops once `trueError ≤ appliedError` — on a set
computed under the very confinement it checks. That circularity is a gap in the argument, not by
itself a miss. Given sound enclosures of the linearized run, a locally Lipschitz field and a
remainder bound `trueError` valid on the box of `Rmax`, the check does confine every run. This is an
argument, not formalized here. The field with its remainder clipped to `[-trueError, trueError]` and
read at the projection onto that box is Lipschitz, so it has a run on `[0, Δt]`. That run is a
linearized run with input in `appliedError`'s box, so it stays in `Rmax`, where it is a run of `f`,
hence by uniqueness the run. The miss is in the bound: `priv_abstrerr_lin` (and
`priv_abstractionError_adaptive`) read the Hessian over `interval(Rmax) + p` only, while a Lagrange
remainder at `x` needs it along the segment from the linearization point `p`, which need not lie in
that box. For `ẋ = 1 - (1001/750) x + (1001/3000) x⁴` from `x(0) = 0` with `Δt = 2`, CORA's own step
(`'lin'`, default `maxError = Inf`) linearizes at `p = 1`, where `f'(1) = 0` and `f(1) = -1/1000`.

**`linReach` — cora-issue, the Hessian region, continued.** The linearized run drifts away from `p`,
the box is about `[-1/500, 2·10⁻⁵]`, `f''` there is below `2·10⁻⁵` while it reaches `4` on `[0, 1]`,
the bound `≈ 8·10⁻⁶` passes the check on the loop's second pass, and `Rti` ends below `1/50000`,
while the run is at `x(1/4) ≥ 1/20`. The adaptive step (`linReach_adaptive`) is fooled the same way
despite its tuning. Take `ẋ = 1 - (59049/39400) x + (468559/236400) x⁶ - (40951/27580) x⁷` from `0`
with `tFinal = 200`. Then `f'` vanishes at both points it linearizes at (`p = 1` for the horizon
`Δt = 2`, `p = 9/10` for `9/5`), and both loops read `f''` near `0` only. The gain `varphi ≈ 113`
makes `aux_optimaldeltat` keep the horizon, and the returned `Rti` ends below `1/50000` while the
run is at `x(1/4) ≥ 1/20`. Confinement here comes from an a priori ball about the step's start,
which the field cannot cross within the step, and the remainder is bounded over a region holding the
expansion point.

**`linReach` — cora-issue, the third-order tensor.** The generated `thirdOrderTensor_` file returns
`T{i,j}`, the third derivative of `fᵢ` along column `j` of `z = [x; u]`, for every column, and
`ind{i}`, the columns where it is non-zero (`write3rdOrderTensorFile.m`). `priv_abstrerr_lin`'s
`tensorOrder == 3` branch loops `for j=1:length(ind{i})` and adds `dz.'*T{i,j}*dz * dz(j)`, the
position `j` read as a column, where `priv_abstrerr_poly` and
`@nonlinearSysDT/priv_linError_thirdOrder` use `T{i,ind{i}(j)}` and `dz(ind{i}(j))`. Whenever
`ind{i}` is not `1:k` the remainder sums the wrong tensors. For `ẋ = (x₂³, 0)` from `{0} × [-1, 1]`
(`alg = 'lin'`, `tensorOrder = 3`, `U = {0}`), `ind{1} = [2]`. The loop reads `T{1,1} = 0`, so the
remainder is `0`. At `p = 0` the Jacobian and the Hessian vanish, so the loop accepts on its first
pass and CORA's `Rti` and `Rtp` keep `x₁` at `0` for every `Δt > 0`, for any interval kernel mapping
a zero factor to `0`, while the run `(t, 1)` from the initial set is at `x₁(Δt) = Δt`. `p` lies in
the box the tensor is read over, so this is the index, not the region ([`nonlinearSys`
`linReach_adaptive`](nonlinearSys.md)). `reachInner` (`linReachInner`) calls the same branch.

**`linReach` — cora-issue, the third-order tensor, continued.** `priv_abstractionError_adaptive`
(`'lin-adaptive'`, `tensorOrder = 3`) takes the right tensor `T{i,ind{i}(j)}` but the wrong factor
`dz(j)` (l. 171; `linReach_adaptive` selects `tensorOrder = 3` at l. 449, 460, 492-539). For the
same `ẋ = (x₂³, 0)` over `{0} × [-1, 1]` at `p = 0` the factor read is `dz(1)`, the `x₁` range
`[0, 0]`, so the returned `err` (`abstrErrAdaptiveTensor3Cora2D`, with the order reductions and the
interval kernels as arguments, a zero factor mapped to `[0, 0]`) is `0` in the first coordinate. At
`(0, 1)` in the set the remainder of `f₁` is `1`, so the error does not enclose it. Witnessed at the
abstraction error only. The adaptive step model is 1D at `tensorOrder = 2`, so no step-level miss is
stated.

**`linReachInner` — CORALean's `linReachInner`.** CORALean's `NonlinearSys.linReachInner` is CORA's
step over exact sets with the exact Minkowski difference and `Rti = Rinit ∪ Rtp` in place of (23),
its `Rtp` and `Rti` proved inside the reachable set
(`NonlinearSys.linReachInner_subset_reachSetExact`,
`NonlinearSys.linReachInner_Rti_subset_reachSetExact`), and the `'minkdiff'` loop
`NonlinearSys.reachInnerMinkdiff` inner at every cell
(`NonlinearSys.reachInnerMinkdiff_subset_reachSetExact`), each step under `Prop. 1`'s hypotheses.
CORALean replaces both: the step is CORA's line by line over exact sets (box, linearization point
`c + ½Δt f(c)`, `e^{AΔt}`, `Rcon`, `C`, the box `Rlinti`, the `while perfIndCurr > 1` loop with
fuel, `Rerror`), its subroutines supplied as `LinReachInnerOps`. `Rtp = minkDiff(Rlintp, Rerror)`
with the exact Minkowski difference, proved inside `R(Δt)` from `Rinit` (Prop. 1, `Rerror` symmetric
about the origin as CORA assumes). `Rti` is `Rinit ∪ Rtp` in place of the Prop. 2 hull, proved
inside `R([T, T+Δt])` when `Rinit ⊆ R(T)`. Hypotheses: Prop. 1's per step (`IsLinReachInnerCert`:
solutions exist, the field Lipschitz along them, `Rerror` convex, compact, nonempty, symmetric, and
the representation (21)).

**`linReachInner` — CORALean's `linReachInner`, continued.**
`IsLinReachInnerCert.of_abstractionError` derives (21) from an `IsAbstractionError` certificate for
`VerrorDyn`, the confinement to CORA's `Rmax` a hypothesis as in every conservative-linearization
step.

**`linReachInner` — cora-issue, (23).** CORA's `@contDynamics/linReachInner.m`, the step of
`priv_reachInnerMinkdiff.m`, returns as `Rti` the exact constrained-zonotope hull of
`minkDiff(minkDiff(Rinit, C) + 2 center(C), Rerror)` and `minkDiff(Rtp.set, C) + 2 center(C)`, which
is (23) of [Wetzlinger-Kulmburg-Althoff L-CSS 2024,
`Prop. 2`](../../2024/wetzlinger-lcss-inner-minkowski-difference.md), false even for the convex
start sets CORA passes. For `f(x) = (x₂, 0)`, `R0 = [-1/10, 1/10] × [-1, 1]` and `timeStep = 1`: the
linearization point is `0`, the constant input `0`, the Hessians vanish so `Rerror = 0`, `A² = 0`
makes `F = 0` (`priv_correctionMatrixState` with truncation `Inf` sums `Aⁱ`, `i ≥ 2`) so `C = 0`,
and `minkDiff` by a point is a translation. So `Rti = conv(R0 ∪ [1 1; 0 1] R0)`, which holds
`(1/2, 0)`, on no run (read from the source, not run).

**`linReachInner` — cora-issue, `minkDiff` without a method.** `@contDynamics/linReachInner.m` calls
`minkDiff` with no method (ll. 137, 144-145) for its inner time-point set
`Rtp.set = minkDiff(R_lin + p, R_err)` and for `Rstart_ti` and `Rend_ti`, the two ends of `Rti`.
Wetzlinger–Kulmburg–Althoff L-CSS 2024's `Prop. 1` (through `Lemma 1`) places only the exact
`R_aff ⊖ R_err` (+ `2c`) inside the reachable set, so in `n ≥ 3` `Rtp` and the time-interval sets
can therefore leave the reachable set even when `Lemma 1`'s hypotheses hold. The default `'approx'`
of `@zonotope/minkDiff.m` is unsound, see the [`zonotope` `minkDiff`](../contSet/zonotope.md) row.
CORALean's difference is `minkDiffRep` ([`zonotope` `minkDiff`](../contSet/zonotope.md)).

**`observe` — float layer.** the strip-based observer with intersection types 1 and 2 at every gain
(`observeStripBased`, generic over the scalar and the set classes, at `Float.Zonotope`), the
set-propagation observer (`observePropagationFloat`) and the interval observer
(`observeIntervalFloat`, whose nominal estimate is a box since `A x + B u + L (y - C x)` is not
exact at a float), each in directed rounding with an outer theorem. The interval observer is
enclosed under `x0 - center(R0) ∈ R0`, as at ℝ.

**`outputSet` — cora-issue account.** CORA's `@contDynamics/outputSet.m` (`aux_outputSet`, l.
80-145), which `reach` of `nonlinearSys` and `nonlinParamSys` calls for every time-point and
time-interval output (`@contDynamics/reach.m` l. 106, 132-133, 182-183), sets `U = params.U`,
`p_u = center(U)` and returns `out_mFile(p_x,p_u) + J (R - p_x) + D_lin (U - p_u)` plus higher-order
terms over `I_u = interval(U)`. But `validateOptions` has run `postProcessing`, whose
`aux_set_U_uTrans_uTransVec` (l. 202-220) moves `center(U)` into `params.u`, then `uTrans`, and
re-centers `params.U` at the origin. `aux_outputSet` never reads `uTrans`, so the output equation is
evaluated at inputs shifted by `-center(U)`. `@nonlinDASys/outputSet.m` (l. 47) does add
`params.uTrans`. For `ẋ = 0`, `y = x + u` (affine, so `out_isLinear`, at either
`tensorOrderOutput`), `R0 = {0}`, `U = {1}`, the default `u = 0`, the output at time `0` is `1` and
CORA's set is `{0}`. Formalized as the `out_isLinear` branch after `postProcessing`
(`NonlinearSys.outputSetCora`), with the counterexample on a run. Read from the source, not run.

**`observe` — the witness.** The counterexample theorems are in the [`linearSysDT`
`executeObserver`](linearSysDT.md) row, for the interval observer
[`LinearSysDT.observeInterval_cora_counterexample`](../../../src/CORALean/ContDynamics/LinearSysDT/Counterexamples/Real/ObserveIntervalCora.lean)
among them.
