# Reachability Analysis and its Application to the Safety Assessment of Autonomous Cars

M. Althoff. "Reachability Analysis and its Application to the Safety Assessment of
Autonomous Cars". PhD thesis, TU München, 2010.

**Source:** https://mediatum.ub.tum.de/doc/1287517 (mediaTUM record 1287517, served as PDF; read directly with a custom PDF-content-stream text extractor since no PDF rasterizer was available in this environment — poppler/pdftoppm and pypdf are not installed here, and Read's PDF-page mode depends on pdftoppm)  
**Inventory:** confirmed (Chapter 3 read cover-to-cover, pp. 28-86 of the thesis = PDF pages 46-104)

Chapter 3 is where continuous-time reachability in CORALean comes from: the
truncated exponential with a tail bound, the correction matrices that pay for
linear interpolation over a step, and the input solution a step's enclosure is
built on. §3.3 is the uncertain-parameter case, which `LinParamSys` follows at
an interval matrix and a matrix zonotope; §3.5.5 is where `ZonoBundle` comes
from. A monograph thesis rather than a cumulative one, so it *is* the source
for much of this and citing it is correct, not a fallback.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 3.1` | Reachable set at a point in time r: the set of states x(r) reachable from X0 under some admissible input/parameter trajectory. | [`ReachSet.lean`](../../src/CORALean/ContDynamics/LinearSys/ReachSet.lean) |
| `Def. 3.2` | Reachable set of a time interval [0,r]: the union of point-in-time reachable sets R(t) for t in [0,r]. | — |
| `Sec. 3.2` | Linear systems whose parameters are certain: the model, its discretization, and what one step of it is built from. | [`LinearSys.lean`](../../src/CORALean/ContDynamics/LinearSys/LinearSys.lean), [`DiscretizeEnclosure.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/DiscretizeEnclosure.lean), [`LinearSysDT.lean`](../../src/CORALean/ContDynamics/LinearSysDT/LinearSysDT.lean) |
| `Eq. 3.2–3.3` | The matrix exponential truncated at order η, widened by a bound on everything past it. | [`Enclosures.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Enclosures.lean), [`ExpEnclosure.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpEnclosure.lean), [`NormExpSubExpTaylorLe.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/NormExpSubExpTaylorLe.lean) |
| `Prop. 3.1` | Gives the interval matrix F (via a truncated Taylor series plus remainder E(r)) bounding the enlargement F·x(0) needed so the linear interpolation of the homogeneous solution encloses all trajectories on [0,r]. | [`ConstCorrectionMatrix.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ConstCorrectionMatrix.lean), [`CorrCoeffBound.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/CorrCoeffBound.lean), [`CorrectionMatrix.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/CorrectionMatrix.lean), [`ExpDiff.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpDiff.lean) |
| `Thm. 3.1` | Over-approximation formula for the reachable set P_R(r) of the inhomogeneous (input) solution, as a truncated Taylor series in A times U plus a remainder term E(r)·r·U. | [`InputSolution.lean`](../../src/CORALean/ContDynamics/LinParamSys/Operations/InputSolution.lean), [`InputSolution.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/InputSolution.lean), [`StepInputOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/StepInputOuter.lean), [`TimePointStepOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimePointStepOuter.lean), [`WeightedIntegral.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/WeightedIntegral.lean) |
| `Prop. 3.2` | P_R(kr+Δt) = e^{Ar} P_R((k-1)r+Δt) + P_R(r), giving the recursive/algorithmic separation of the input solution across time steps. | [`InputReachSeparation.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputReachSeparation.lean) |
| `Cor. 3.1` | Special case of Prop. 3.2: P_R(r+Δt) = e^{Ar} P_R(Δt) + P_R(r). | — |
| `Alg. 1` | "Compute H_R(0,t_f)": wrapping-effect-free algorithm for the reachable set of the homogeneous solution of an LTI system (no input) using the convex-hull + correction-matrix construction. | — |
| `Alg. 2` | "Compute R(0,t_f)": wrapping-effect-free algorithm for the full reachable set of an LTI system with input, valid when 0 ∈ U, using box() on the input-solution part to keep zonotope order bounded. | [`TimeIntervalOuterConvexCompact.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimeIntervalOuterConvexCompact.lean) |
| `Prop. 3.3` | If 0 ∈ U, the inhomogeneous reachable set is monotonically enclosing over time: P_R(r) ⊆ P_R(r+Δt) for 0 < Δt ≤ r. | [`ConstTrajectoryInputSolutionTimeIntervalOuter.lean`](../../src/CORALean/ContDynamics/LinParamSys/Theorems/ConstTrajectoryInputSolutionTimeIntervalOuter.lean), [`InputReachMono.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputReachMono.lean), [`TimePointStepOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimePointStepOuter.lean) |
| `Alg. 3` | "Compute R(0,t_f)": extension of Alg. 2 to input sets U not containing the origin, by splitting U into a constant part and a zero-containing part. | — |
| `Sec. 3.3` | Linear systems whose parameters are uncertain. | [`LinParamSysDT.lean`](../../src/CORALean/ContDynamics/LinParamSysDT/LinParamSysDT.lean) |
| `Sec. 3.3.1` | The uncertainty as an interval matrix: enclosing e^{AΔt} and the correction matrices over one. | [`API.lean`](../../src/CORALean/ContDynamics/LinParamSysDT/Theorems/API.lean), [`IntervalCorrection.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/IntervalCorrection.lean), [`IntervalEnclosures.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/IntervalEnclosures.lean), [`ExpIntervalEnclosure.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpIntervalEnclosure.lean) |
| `Lemma 3.1` | Gives an exact (single-use-expression, hence non-over-approximating) interval-arithmetic formula for W(t) = At + (1/2)A²t² when A is an interval matrix. | — |
| `Thm. 3.2` | Over-approximation e^{AΔt}_κ of the interval matrix exponential via a κ-th order Taylor expansion, using the exact 2nd-order term from Lemma 3.1 plus interval-arithmetic higher-order terms and remainder E(t). | — |
| `Lemma 3.2` | Symmetric interval matrix S = [-S,S] times a regular matrix M satisfies M∘S = [- \| M \| S, \| M \| S] (elementwise absolute value); used to bound linear maps by symmetric interval matrices. | — |
| `Lemma 3.3` | Formula for the over-approximating zonotope resulting from the linear map of a zonotope Z by a symmetric interval matrix S = [-S,S], expressed via new generators f^(i) derived from Lemma 3.2. | — |
| `Thm. 3.3` | Formula for the over-approximating zonotope resulting from the linear map of a zonotope Z by a general interval matrix L = [L-S, L+S] (L regular part + symmetric interval part S), combining Lemma 3.3 with the regular-matrix map. | [`MtimesIntervalMatOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MtimesIntervalMatOuter.lean) |
| `Prop. 3.4` | Gives the interval matrix ~F (input correction matrix, computed via a Taylor-series/remainder formula analogous to Prop. 3.1) bounding the enlargement ~F·~u needed for the constant-input part when 0 ∉ U. | — |
| `Alg. 4` | "Compute R(0,t_f)": algorithm for LTI systems with the system matrix bounded by an interval matrix A (not wrapping-effect free), combining e^{AΔt} (Thm. 3.2), the interval-matrix zonotope map (Thm. 3.3), correction matrices F, ~F, and periodic zonotope order reduction. | — |
| `Sec. 3.3.2` | The uncertainty as a matrix zonotope, which keeps the dependency between entries that an interval matrix loses. | [`IntervalEnclosures.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/IntervalEnclosures.lean), [`DiscretizeMatZonotope.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/DiscretizeMatZonotope.lean) |
| `Prop. 3.5` | "Matrix Zonotope Map": over-approximating zonotope resulting from the product of a matrix zonotope L_Z (center L^(0), generators L^(i)) and a zonotope Z, obtained by concatenating the generators of L^(0)Z, L^(1)Z, …, L^(κ)Z. | [`MtimesMatZonotopeOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MtimesMatZonotopeOuter.lean) |
| `Prop. 3.6` | "Reachable Set of the Input Solution": adapts Thm. 3.1's input-solution over-approximation to the case where the system matrix is a matrix zonotope A_Z (exact for the linear/quadratic terms, interval-matrix over-approximation for higher powers). | — |
| `Sec. 3.4` | Nonlinear systems by conservative linearization: a linear part plus a set enclosing the abstraction error. | [`AbstractionError.lean`](../../src/CORALean/ContDynamics/NonlinearSys/AbstractionError.lean) |
| `Prop. 3.7` | "Over-approximation of the Set of Linearization Errors": bounds \| L_i \| ≤ [0, l_i] for the Lagrange remainder of the linearized nonlinear system, given the reachable zonotope Ẑ and parameter box P, via a max-norm/Jacobian bound. | — |
| `Cor. 3.2` | "Optimal Linearization Point": the bound l of Prop. 3.7 is minimized by choosing the linearization point z* equal to the center c of the reachable zonotope Ẑ. | — |
| `Prop. 3.8` | "Splitting of Zonotopes": a zonotope Z can be split along its j-th generator into two zonotopes Z1, Z2 with Z1 ∪ Z2 = Z and Z1 ∩ Z2 = Z* (Z with the j-th generator removed). | [`Split.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Split.lean), [`SplitUnion.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SplitUnion.lean), [`SplitIntersection.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SplitIntersection.lean) |
| `Alg. 5` | "Compute R'_j within a location y_i": computes the continuous reachable set within one hybrid-automaton location up to leaving the invariant, and the enclosed intersection R_j with a guard set, using reach(), halfspaceConv(), intersectionTimes(), generatorConv(). | — |
| `Sec. 3.5.5` | Several enclosing zonotopes at once, denoting their intersection — the zonotope bundle. Prose only; no numbered result of its own. | [`API.lean`](../../src/CORALean/ContSet/ZonoBundle/API.lean), [`ZonoBundle.lean`](../../src/CORALean/ContSet/ZonoBundle/Float/ZonoBundle.lean), [`ZonoBundle.lean`](../../src/CORALean/ContSet/ZonoBundle/Real/ZonoBundle.lean) |
| `Def. 3.3` | "Hybrid Automaton": formal tuple HA = (Y, y0, X, X0, U, P, inv, T, g, h, f) with locations, invariants (polytopes), guard sets (polytopes), linear jump map x' = K x + k, and flow function f. | [`HybridAutomaton.lean`](../../src/CORALean/HybridDynamics/HybridAutomaton.lean) |
| `Def. 3.4` | "Exact Continuous and Discrete Reachable Set": extends Def. 3.1's reachable-set definition to hybrid automata, defining the continuous reachable set R_e(r) and discrete (location) reachable set R_z(r). | — |
| `Remark 3.1` | Notes the interval-matrix result of Lemma 3.2 is an exact interval enclosure, but the true image set (e.g. a line segment) need not itself be an interval matrix. | n/a — a remark on the construction, not a result |
| `Remark 3.2` | Notes that the over-approximation in the proof of Lemma 3.3 coincides with the simpler enclosure S·box(Z) (comparing to Prop. 2.2). | n/a — a remark on the construction, not a result |
| `Remark 3.3` | "Interval Matrix vs. Matrix Zonotope": discusses when to prefer the interval-matrix methods of §3.3.1 vs. the matrix-zonotope methods of §3.3.2 (independent vs. few-parameter uncertainty, accuracy/cost tradeoffs). | n/a — a remark on the construction, not a result |
| `Heuristic 3.1` | "Generator Selection for Splitting of Reachable Sets": performance measure ϱ_j = max(l1,j/l̄) − max(l2,j/l̄) used to pick which generator j to split when the admissible linearization-error bound is exceeded. | — |

## Findings

[FINDINGS.md](../../FINDINGS.md) — **Prop. 3.1**: the printed proof pulls one
`[−1,1]` out of two independent remainders and the bound does not follow. The
proposition is true; the argument for it here is a different one.

[FINDINGS.md](../../FINDINGS.md) — **Prop. 3.8**: the intersection is derived
from `A + (B ∩ C) = (A + B) ∩ (A + C)`, which no pair of sets need satisfy. The
proposition is true; convexity of `Z*` is what carries the step.
