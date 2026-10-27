# contDynamics/@nonlinearSys

CORA methods of `contDynamics/@nonlinearSys/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `NonlinearSys`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `display` | out-of-scope | n/a — plotting/display |  |
| `eq` | out-of-scope | n/a — matlab-runtime |  |
| `falsify` | out-of-scope | n/a — solver-dependent | optimisation and wall-clock search for a falsifying trajectory |
| `getPrintSystemInfo` | out-of-scope | n/a — plotting/display |  |
| `getfcn` | out-of-scope | n/a — matlab-runtime |  |
| `identify` | proved | [`NonlinearSys.identify`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/Identify.lean), [`NonlinearSys.identifyCandidate`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/IdentifyCandidate.lean), [`NonlinearSys.identifyCandidate_fit`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/IdentifyCandidateFit.lean), [`NonlinearSys.identify_le_candidate`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/IdentifyLeCandidate.lean) | partial: algorithm `dmd` only, real layer (`noncomputable`), not float. The basis `φ` (`options.basis`, `options.phi`) and the SVD `X1 = V S Wᵀ` of its values at the data are arguments (a factorization, not computed), and so is `computeError` (`err`, compared by `lt`); the data points come as `dx`, whose finite differences (`getDataPoints`) are not modelled. Guarantees, both about the data and not the dynamics: if the data obeys `ẋ = A' φ(x, u)` for some `A'`, the full-rank candidate reproduces `dx` at every point exactly; and the system returned has `err` no larger than any rank's candidate. Details below. |
| `initReach` | float | [`NonlinearSys.linearize`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/Linearize.lean), [`NonlinearSys.linReachPoly`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachPoly.lean), [`NonlinearSys.IsTrajectory.linReachPoly_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachPolyOuter.lean) · float: [`NonlinearSys.FloatHessModel.linReachFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachFloat.lean), [`NonlinearSys.FloatHessModel.Encloses.linReachFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinReachFloatOuter.lean), [`NonlinearSys.FloatHessModel.abstrErrPolyFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrErrPolyFloat.lean), [`NonlinearSys.FloatHessModel.Encloses.abstrErrPolyFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstrErrPolyFloatOuter.lean) | route a — the first step of `linReach` at `alg = 'lin'` or `'poly'` through a `FloatHessModel` of `f` (a `FloatModel` with interval Hessians); the `'poly'` dynamic error is the second-order Lagrange form, not CORA's third-order tensor |
| `initReach_adaptive` | float | [`NonlinearSys.adaptInit`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptInit.lean), [`NonlinearSys.adaptStep`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptStep.lean), [`NonlinearSys.adaptStep_invariant`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdaptStepInvariant.lean) · float: [`NonlinearSys.adaptInit`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptInit.lean), [`NonlinearSys.FloatHessModel.adaptStepFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptStepFloat.lean), [`NonlinearSys.FloatHessModel.Encloses.adaptStepFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdaptStepFloatOuter.lean) | route a — outer: the first state is `adaptInit` itself, generic in the set representation and run as is at `Zonotope (Vec 𝕋 n)`; each step after it is `adaptStepFloat` from a `FloatHessModel` of `f`, the full step of `orderStepFloat` at the time step the tuning chose, and `Encloses.adaptStepFloat_outer` places every run of the real system in the step's window |
| `isequal` | out-of-scope | n/a — matlab-runtime |  |
| `linReach_adaptive` | float | [`NonlinearSys.aux_adaptLinPass`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptStep.lean), [`NonlinearSys.IsTrajectory.confinement_of_subset`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ConfinementOfSubset.lean), [`NonlinearSys.reachSetExact_confinement_of_subset`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachSetExactConfinementOfSubset.lean) · float: [`NonlinearSys.FloatModel.adaptLinPassFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptLinPassFloat.lean), [`NonlinearSys.FloatModel.adaptLinPassFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdaptLinPassFloatOuter.lean) | CORALean takes confinement from an a priori ball about the step's start (the `cora-issue` note of this row); cora-issue — the adaptive step reads the Hessian over `interval(Rmax) + p` only and takes the wrong tensor factor, as `linReach` does; counterexample theorems for both are in the [`contDynamics` `linReach`](contDynamics.md) row ([`NonlinearSys.linReachAdaptiveCora1D_hessianRegion_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachAdaptiveCora1D.lean), [`NonlinearSys.linReachAdaptiveCora1D`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachAdaptiveCora1D.lean), [`NonlinearSys.linReachCora1D_hessianRegion_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/LinReachCora1D.lean), [`NonlinearSys.IsTrajectory.confined_of_ball`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ConfinedOfBall.lean)). Details below. |
| `linearize` | float | [`NonlinearSys.linearize`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/Linearize.lean), [`NonlinearSys.IsTrajectory.linearize`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/Linearize.lean), [`NonlinearSys.IsTrajectory.linearize_horizon`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinearizeHorizon.lean) · float: [`NonlinearSys.FloatModel.linearizeFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinearizeFloat.lean), [`NonlinearSys.FloatModel.linInputFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinInputFloat.lean), [`NonlinearSys.FloatModel.Encloses.linInputFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LinInputFloatOuter.lean) | route a through a `FloatModel` of `f` (interval extensions of `f` and its Jacobian blocks, tied to `f` by `Encloses`); the remainder is first order in the deviation, or CORA's Hessian bound with a `FloatHessModel` (`FloatHessModel.hessRemainder`, `Encloses.hessRemainder_abstractionError`) |
| `ne` | out-of-scope | n/a — matlab-runtime |  |
| `nonlinearSys` | proved | [`NonlinearSys.toNonlinParam`](../../../src/CORALean/ContDynamics/NonlinParamSys/Operations/ToNonlinParam.lean), [`NonlinearSys.IsTrajectory.toNonlinParam`](../../../src/CORALean/ContDynamics/NonlinParamSys/Theorems/IsTrajectoryToNonlinParam.lean) | conversion to `NonlinParamSys`: every trajectory is one of the image |
| `post` | float | [`NonlinearSys.relinTimeInterval`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/RelinTimeInterval.lean), [`NonlinearSys.relinDeltaReach`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/RelinDeltaReach.lean), [`NonlinearSys.IsTrajectory.relinTimeInterval_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinTimeIntervalOuter.lean), [`NonlinearSys.IsTrajectory.relinDeltaReach_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinDeltaReachOuter.lean) · float: [`NonlinearSys.FloatModel.relinStepFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/RelinStepFloat.lean), [`NonlinearSys.FloatModel.Encloses.relinStepFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinStepFloatOuter.lean), [`LinearSys.postDeltaFloat`](../../../src/CORALean/ContDynamics/LinearSys/Operations/PostDeltaFloat.lean), [`LinearSys.IsCanonicalTrajectory.postDeltaFloat_outer`](../../../src/CORALean/ContDynamics/LinearSys/Theorems/IsTrajectoryPostDeltaFloatOuter.lean) | route a — a step runs in floats as `relinStepFloat`, or `FloatHessModel.linReachFloat` at either `alg`; `relinDeltaReach`'s differences as `postDeltaFloat` |
| `reachInner` | proved | [`NonlinearSys.reachInnerMinkdiff`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/ReachInnerMinkdiff.lean), [`NonlinearSys.aux_reachInnerMinkdiffLoop`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/ReachInnerMinkdiff.lean), [`NonlinearSys.reachInnerMinkdiff_subset_reachSetExact`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachInnerMinkdiffSubsetReachSetExact.lean), [`NonlinearSys.reachInnerMinkdiff_subset_reachSetExact_horizon`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachInnerMinkdiffSubsetReachSetExactHorizon.lean), [`NonlinearSys.linReachInner`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinReachInner.lean) | the `reachInner` row covers `'minkdiff'` only. cora-issue — CORA's `reachInner` is unsound or crashes in five ways. `priv_reachInnerParallelotope.m` takes the box of independently chosen components. `priv_reachInnerProjection.m` stores the whole line for a proper Kaucher result and returns the box of the components. `priv_reachInnerScaling.m` skips the backward simulation of one point and so can return an unchecked set. `linReachInner.m` returns the hull of (23). `checkDynParameterOptions.m` rejects every `timeStepInner` through a misspelled variable ([`NonlinearSys.reachInnerScalingCora1D_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ReachInnerScalingCora1D.lean)). Details below. |
| `reach_adaptive` | float | [`NonlinearSys.adaptRun`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptRun.lean), [`NonlinearSys.relinReach`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/RelinReach.lean), [`NonlinearSys.reachSetExact_subset_relinReach`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachSetExactSubsetRelinReach.lean), [`NonlinearSys.IsTrajectory.relinReach_evalOn`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinReachEvalOn.lean), [`NonlinearSys.IsTrajectory.relinReach_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinReachOuter.lean), [`NonlinearSys.IsTrajectory.relinReach_outer_inputSolution`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinReachOuterInputSolution.lean) · float: [`NonlinearSys.FloatHessModel.adaptRunFloat`](../../../src/CORALean/ContDynamics/NonlinearSys/Operations/AdaptRunFloat.lean), [`NonlinearSys.FloatHessModel.Encloses.adaptRunFloat_outer`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdaptRunFloatOuter.lean) | route a — outer: [Wetzlinger et al. 2022]'s adaptive loop runs in floats as `NonlinearSys.FloatHessModel.adaptRunFloat` from a `FloatHessModel` of `f`, each step the full step of `orderStepFloat` at the time step the tuning chose (a checked region, not the paper's fixed-point abstraction error), and `Encloses.adaptRunFloat_outer` places every run of the real system in the window of its step. The tuning cannot affect it. The real side is the re-linearization loop at caller-supplied certificates, `adaptRun` with `relinReach_outer`, and `NonlinearSys.FloatModel.reachFloat` (`Encloses.reachFloat_outer`) is its fixed-step float form |
| `simulate` | — | — | R-CTSIM: calls `ode45` |
| `taylor` | out-of-scope | n/a — matlab-runtime | symbolic derivative code generation (m-file, function handle) |

## Details

**`identify` — not formalized.** No claim that the fit is least-squares for inconsistent data or
that a small `err` means a good model. `'opt'` (`fmincon`) and `'nested'` are not formalized.
`'sparse'` (SINDy) is not formalized as CORA runs it: `priv_identifySparse` calls MATLAB's `lasso`
on every row of `ẋ` (solver-dependent) and refits the surviving terms by the dynamic mode
decomposition above, whereas the sequential thresholded least squares of [Brunton et al.
2016](../../2016/brunton-pnas-sindy.md) (`Code 1`) is formalized on its own page (`sindy`, with its
fixed-point guarantees) and is not what CORA runs.

**`identify` — the `'dmd'` fit.** The `'dmd'` fit is the stacked-snapshot candidate of [Proctor et
al. 2016](../../2016/proctor-siads-dmd-control.md) (`Eq. 26`, `Eq. 28`: one SVD of the regressors,
the state and input blocks read off), with a constant `1` in the regressor for the offset `c` the
paper does not have. The paper's output SVD and reduced-order model are not part of `identify`. Its
full-rank properties, including `Ā = X' X†` (`dmdCandidate_eq_mul_pinv`), are on that page.

**`linReach_adaptive` — float layer.** route a — outer: the linear pass runs in floats as
`adaptLinPassFloat`, and `adaptLinPassFloat_outer` places every run whose field less its linear part
stays in the pass's input `f(z✱) ⊕ B(U - u✱)` in its two sets (the abstraction error is not part of
the pass).

**`reachInner` — cora-issue, `priv_reachInnerParallelotope`.** CORA's
`@nonlinearSys/private/priv_reachInnerParallelotope.m` (`aux_innerApprox`) computes, for each output
component `i` separately, Goubault and Putot's `Thm. 2` interval with each input `j` in turn as the
existential one and keeps the widest, then returns the box of the components. [Goubault-Putot L-CSS
2020, `Thm. 3`](../../2020/goubault-lcss-robust-underapproximations.md) puts that box in the image
only when each input is existential in one component (`π` a map), which the independent choice does
not ensure. Take `f(x) = (x₀, x₀ + x₁/100)` on `[-1, 1]²`, the time-`1` flow of a linear system.
Both components pick `x₀`, and the Jacobian center's condition number (about `200`) is over CORA's
`100` so no preconditioning is applied. CORA returns `[-1, 1] × [-0.99, 0.99]`, though `(1, -0.99)`
is not reached (read from the source, not run). Not formalized beyond the counterexample.

**`reachInner` — cora-issue, `priv_reachInnerProjection`.** CORA's
`@nonlinearSys/private/priv_reachInnerProjection.m`, the implementation of [Goubault-Putot HSCC
2017, `Alg. 1`](../../2017/goubault-hscc-forward-inner-reachability.md), has two defects in Step 3.
A component whose Kaucher result (18) is proper has an empty inner approximation, but CORA's
`intKaucher/isProp` returns `inf >= sup` (improper, despite its name and comment), and the branch
for `~isProp` stores `interval(-inf, inf)`, the whole line, which no bounded reachable set contains.
For `ż = 0` on `[0, 1]` with `z̃₀ = ½`, the sound enclosures `[z̃] = [-1, 2]` and `[J] = [1, 1]`
give the proper `[-½, 3/2]`, and CORA reports `ℝ` for the range `[0, 1]`. And the result stored as
the inner approximation is the box of the components, while (18) is an inner approximation of each
component's projection only: for the time-`1` flow `((x₀ + x₁)/2, (x₁ - x₀)/2)` on `[-1, 1]²` both
components are `[-1, 1]` and `(1, 1)` is not reached (read from the source, not run). Formalized:
(18) per component with its inner theorem, and both counterexamples.

**`reachInner` — cora-issue, `linReachInner`.** The account of (23) is in the [`contDynamics`
`linReachInner`](contDynamics.md) row.

**`reachInner` — what CORALean proves for `'minkdiff'`.** CORALean's `NonlinearSys.linReachInner` is
CORA's step over exact sets with the exact Minkowski difference and `Rti = Rinit ∪ Rtp` in place of
(23), its `Rtp` and `Rti` proved inside the reachable set
(`NonlinearSys.linReachInner_subset_reachSetExact`,
`NonlinearSys.linReachInner_Rti_subset_reachSetExact`), and the `'minkdiff'` loop
`NonlinearSys.reachInnerMinkdiff` inner at every cell
(`NonlinearSys.reachInnerMinkdiff_subset_reachSetExact`), each step under `Prop. 1`'s hypotheses.

**`reachInner` — cora-issue, `priv_reachInnerScaling`.** CORA's
`@nonlinearSys/private/priv_reachInnerScaling.m`, the implementation of [Kochdumper-Althoff CDC
2020](../../2020/kochdumper-cdc-nonconvex-inner.md), runs Steps 1-3 (lines 65-146) and returns
`getSubset(R,1:n,I)` without its independent generators (lines 150-152), but never the paper's Step
4, the backward simulation (14) of one point. Nothing else does (`reachInner.m` only dispatches).
That check supplies `Thm. 1`'s `C ∩ R ≠ ∅`, and nothing in the code replaces it. Two paths reach an
unchecked set. At the default `scaleFac = 'auto'` a failed contraction lowers `factor` by `0.01` and
restarts the boundary loop with `I` as it is. When `factor` reaches `0` the `while` (line 111) ends
with `I` certified for none or only some pieces, and line 150 returns it as an inner approximation
instead of the empty set the fixed-`scaleFac` branch (line 141) gives. And the constraint
`aux_constraintIntersection` (lines 216-217) and the result (line 152) use the dependent part `R.G`
only, so the outer-approximation property (6), which holds with `R.GI`, does not put any point of
the result in `R`.

**`reachInner` — cora-issue, `priv_reachInnerScaling`, continued.** For `ẋ = 0` from `X₀ = [-1, 1]`
and the outer approximation `2 + α + 2β` (it holds the run from every `α`, its boundary pieces
`[1, 5]` and `[-1, 3]` hold `∂R = {±1}`), every point `fmincon` may return is in its box, so
`(-1, -1)` solves the first piece's constraint in `[-1, factor·val] × [-1, 1]` and no sound
contractor proves it empty. CORA returns `[1, 3]`, whose point `3` is unreachable and whose center
`2` fails (14). Formalized as CORA computes it in one dimension
(`NonlinearSys.reachInnerScalingCora1D`, `fmincon` and the contractor as arguments) with the
counterexample for every `fmincon` returning a feasible point, every contractor that the paper's
`Def. 3` admits and every number of passes (read from the source, not run). The second path is not
witnessed: in one dimension a certified `I` contains `0`, and at `ẋ = 0` a connected set missing
both pieces that contains `p(0)` is inside `R`.

**`reachInner` — the witnesses.**
([`convexHull_timeInterval_convex_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeIntervalConvex.lean),
[`NonlinearSys.reachInnerScalingCora1D`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ReachInnerScalingCora1D.lean),
[`NonlinearSys.reachInnerScalingCora1D_counterexample`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ReachInnerScalingCora1D.lean),
[`prod_inner_ranges_not_subset_image`](../../../src/CORALean/Global/Counterexamples/ProductInnerRange.lean),
[`aux_kaucher_gain`](../../../src/CORALean/Global/KaucherInner.lean),
[`kaucherInnerStep_cora_counterexample`](../../../src/CORALean/Global/Counterexamples/KaucherInnerCora.lean),
[`kaucherInnerStep_box_counterexample`](../../../src/CORALean/Global/Counterexamples/KaucherInnerBox.lean),
[`NonlinearSys.minkowskiDiff_inputSolution_subset_reachSetExact`](../../../src/CORALean/ContDynamics/NonlinearSys/Theorems/MinkowskiDiffInputSolutionSubsetReachSetExact.lean)).

**`reachInner` — cora-issue, `timeStepInner`.** CORA's
`global/functions/helper/dynamics/checkOptions/checkDynParameterOptions.m`, the case
`'timeStepInner'` of its `switch` (l. 172-173), reads
`checks = aux_getChecksOptions_timeStepInner(charecks,sys,func,params,options);`: `charecks` is no
variable and no function (`checks` is meant), so MATLAB stops with
`Unrecognized function or variable 'charecks'`. `validateOptions` calls the check for every option
the user set that the config file lists, and `config_nonlinearSys_priv_reachInnerScaling.m` (l. 81)
lists `timeStepInner` as `'optional'`, so `reachInner` of a `nonlinearSys` (`algInner = 'scale'`,
`priv_reachInnerScaling.m` l. 45) with any `options.timeStepInner` stops, valid or not. The check,
once reached, tests `rem(params.tFinal,val)` and ignores `tStart`. A MATLAB error, not a wrong
value. Formalized over the names of the options set (`NonlinearSys.validateOptionsCora`, `none` the
error), with a theorem for any list that contains `timeStepInner` (read from the source, not run).

**`reachInner` — cora-issue, `timeStepInner`, continued.**
([`NonlinearSys.validateOptionsCora`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ValidateOptionsTimeStepInnerCora.lean),
[`NonlinearSys.validateOptionsCora_timeStepInner_crash`](../../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ValidateOptionsTimeStepInnerCora.lean)).
