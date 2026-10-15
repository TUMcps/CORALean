# Fully-Automated Verification of Linear Systems Using Reachability Analysis with Support Functions

M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
Linear Systems Using Reachability Analysis with Support Functions". HSCC, 2023, Article 5.

**Source:** https://mediatum.ub.tum.de/doc/1725668/document.pdf — Wetzlinger's thesis, Appendix A.3 (pp. 79–91), a verbatim reprint of the ACM version, read with `pypdf` (poppler is not installed here, so the Read tool's PDF-page mode is unavailable, and the ACM version at https://doi.org/10.1145/3575870.3587121 is paywalled; the paper has no arXiv preprint).  
**Inventory:** confirmed

The support-function sibling of the
[TAC 2023 verification paper](wetzlinger-fully-automated-verification.md): the same
automated verify-or-falsify loop, but computing an upper *and* a lower bound on the
support function of the reachable set in one direction rather than the set itself,
which is what drops the propagation to O(n²) and lets the specification pick the
directions. Its lower bound is the novel part — an inner approximation obtained from
support vectors, computed exactly by simulating the equivalent discrete-time system
under piecewise-constant inputs. The paper states almost nothing as a theorem: five
definitions, a problem statement and three algorithms, with the bounds derived inline
from the cited approximation model, so the count below is small by the paper's own
construction. The one inline construction that is a claim of its own, the explicit
inner approximation of Sec. 4.2 read off simulated support vectors, has its row, and
`Alg. 1` and `Alg. 3` are split where their listings split: `Alg. 1` into the upper
bounds of lines 11-13 and the lower bounds of lines 14-16, `Alg. 3` into its two exits,
with the counterexample of Sec. 5.2, the direction search that feeds them, and the closing
claim that the search always decides (`Alg. 3 (termination)`). What the
tree answers for is the two set representations the paper defines for itself —
polytopes in both forms and ellipsoids, at which the support function is an equality
rather than a bound — and, `LinearSys.IsCanonicalTrajectory` being a Carathéodory run and
`LinearSys.reachSet_eq` an equality, the falsification side: every lower bound is a
value some run of the system takes, and every `unsafe` comes with that run.

`Alg. 3 (termination)` is `false`, and not for want of the convergence of `Alg. 1`'s bounds it
cites [40, Sec. 3] for: the search can stop refining while the bounds are still too loose. Line 15
halves Δt only once the origin lies in `P̂`, the polytope of the *outer* support vectors, but lines
19 and 23 steer the directions by `P̌`, the inner one's; once the inner approximation is separated
from `L` and the outer one still meets it, the directions can settle on the separating one, whose
outer vertices all lie on one side of the origin, and the loop runs forever at that Δt. What the
tree also has is the converse: whatever the search does and however often it halves Δt, an exit it
takes is right (`LinearSys.verifySearch_sound`).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Support function) [cites [31, Sec. 2]] For compact convex S⊂R^n and ℓ∈R^n, ρ(S,ℓ) := max_{x∈S} ℓ^T x and the support vector ν(S,ℓ) := argmax_{x∈S} ℓ^T x, which need not be unique. | n/a — restated from Girard and Le Guernic 2008, which this formalization does not draw on directly | `restated` |
| `Def. 2` | (Zonotope) [cites [30, Def. 1]] Z := {c + Σ_{i=1}^γ G_(·,i) α_i \| α_i∈[-1,1]}, with ρ(Z,ℓ) = ℓ^T c + Σ_i \|ℓ^T G_(·,i)\| and ν(Z,ℓ) = c + Σ_i sgn(ℓ^T G_(·,i)) G_(·,i); shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Def. 3` | (Polytope) Halfspace representation P := {x \| Hx ≤ f} and vertex representation P := {Σ β_i v_i \| Σ β_i = 1, β_i ≥ 0}; for the vertex form the support function is max_i ℓ^T v_i and the support vector the maximizing vertex, for the halfspace form both come from a linear program. Shorthands ⟨H,f⟩_H and ⟨[v_1...v_s]⟩_V. | [`HPolytope.lean`](../../src/CORALean/ContSet/HPolytope/Real/HPolytope.lean), [`SupportBound.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/SupportBound.lean), [`VPolytope.lean`](../../src/CORALean/ContSet/VPolytope/Real/VPolytope.lean), [`SupportBound.lean`](../../src/CORALean/ContSet/VPolytope/Real/Operations/SupportBound.lean), [`SupportBoundAttained.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SupportBoundAttained.lean) — the vertex-form equality needs a nonempty vertex list | `correct` |
| `Def. 4` | (Ellipsoid) For a center c∈R^n and a positive semi-definite shape matrix Q, E := {x \| (x-c)^T Q^{-1} (x-c) ≤ 1}, with ρ(E,ℓ) = ℓ^T c + √(ℓ^T Qℓ) and ν(E,ℓ) = c + Qℓ/√(ℓ^T Qℓ); shorthand E=⟨c,Q⟩_E. | [`Ellipsoid.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Ellipsoid.lean), [`SupportBound.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Operations/SupportBound.lean), [`SupportBoundAttained.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/SupportBoundAttained.lean) | `underspecified` — `Q` is semi-definite but written through `Q⁻¹`, which a singular `Q` does not admit |
| `Def. 5` | (Reachable set) R(t) := {ξ(t,x(0),u(·)) \| x(0)∈X_0, ∀θ∈[0,t]: u(θ)∈U}, with R(t_k) the time-point and R(τ_k) the time-interval solution. | n/a — restated; tracked as `Def. 3.1` on [Althoff's thesis](../2010/althoff-thesis.md) | `restated` |
| `Problem 1` | (Verification) Given an LTI system with X_0, U and V, a safe set K=⟨H,f⟩_H and/or convex unsafe sets L_1..L_b, decide whether ∀t∈[0,t_end]: Y(t) ⊆ K and Y(t) ∩ ⋃_i L_i = ∅. | n/a — the task the paper's algorithms answer, not a claim to formalize | `not-a-claim` |
| `Sec. 4.2` | (Inner approximation from support vectors) The time-point inner approximation is computed exactly via simulation, since its inputs are piecewise constant: with the equivalent discrete-time system x(k+1) = e^{AΔt}x(k) + Tu(k) (Eq. 18, T = A^{-1}(e^{AΔt} − I_n) of Eq. 13), the initial state x(0) = ν(X_0,(e^{At_k})^⊤ℓ) (Eq. 19) and the inputs ∀j∈{0,...,k}: u(j) = ν(U_0,(e^{At_j})^⊤ℓ) + ũ (Eq. 20), the simulated x(k) is the support vector ν(Ř(t_k),ℓ); for template directions ℓ_1,...,ℓ_w, ⟨[ν(Ř(t_k),ℓ_1),...,ν(Ř(t_k),ℓ_w)]⟩_V ⊆ R(t_k). | [`HeldInput.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/HeldInput.lean), [`HeldInputMeasurable.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HeldInputMeasurable.lean), [`HeldSim.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/HeldSim.lean), [`HeldSimEq.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HeldSimEq.lean), [`ClosedFormHeldInput.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ClosedFormHeldInput.lean) (`LinearSys.closedForm_heldInput`: the run under the held inputs, read at t_k, is Eq. (18)'s x(k)), [`TrajectoryHeldInput.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IsTrajectoryHeldInput.lean) (`LinearSys.isTrajectory_heldInput`: that run is a `IsTrajectory`), [`SupportCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/SupportCounterexample.lean) (`LinearSys.supportCounterexample`, Eqs. (19)-(20) with the direction corrected), [`HeldSimLeSupportCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HeldSimLeSupportCounterexample.lean) (`LinearSys.heldSim_le_supportCounterexample`: no initial state of X_0 and no inputs held in U reach further along ℓ at t_k, so x(k) is the support vector), [`HeldSimSupportCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HeldSimSupportCounterexample.lean) (`LinearSys.heldSim_supportCounterexample`: its value along ℓ is line 15 of `Alg. 1`), [`ReachSetConvex.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ReachSetConvex.lean), [`ConvexHullSupportCounterexampleSubsetReachSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ConvexHullSupportCounterexampleSubsetReachSet.lean) (`LinearSys.convexHull_supportCounterexample_subset_reachSet`: the vertex polytope lies in R(t_k)), [`PrintedSupportInput.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/PrintedSupportInput.lean) — `B = I_n`, `p = 0`, and `T` as the series `MatExp.expIntegral`, which needs no A^{-1}. **Counterexample:** `LinearSys.printedSupportInput_counterexample` | `fixed` — Eq. (20) maximizes over U along (e^{At_j})^⊤ℓ, but Eq. (18) carries u(j) to t_k by e^{At_{k-1-j}}T, so the direction has to be (e^{At_{k-1-j}}T)^⊤ℓ: `T` is dropped and the steps are counted from the wrong end; see Findings |
| `Alg. 1 (upper bounds)` | ("Reachability analysis using support functions", lines 1-13) For one direction ℓ, back-propagates the direction by d_{k+1} = (e^{AΔt})^⊤d_k (line 8) and propagates the particular solutions to return the upper bounds ρ(R̂(t_{k+1}),ℓ) = ρ(H(t_{k+1}),ℓ) + ρ(P̂_U(t_{k+1}),ℓ) (line 12) and ρ(R̂(τ_k),ℓ) = max{ρ(H(t_k),ℓ), ρ(H(t_{k+1}),ℓ)} + ρ(C,d_k) + ρ(P̂_U(t_{k+1}),ℓ) (line 13) over the time horizon, with ρ(P̂_U(t_{k+1}),ℓ) = ρ(P̂_U(t_k),ℓ) + ρ(P̂_U(Δt),d_k) (line 11), P̂_U(Δt) by Eq. (16) and the curvature enclosure C = FX_0 ⊕ Gũ by Eq. (14)-(15) (line 5). | [`SupportUpperState.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/SupportUpperState.lean), [`SupportUpper.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/SupportUpper.lean) (`LinearSys.supportUpper`, lines 1-5 and 7-13, one `let` per line), [`SupportUpperOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/SupportUpperOuter.lean) (`LinearSys.supportUpper_outer`: line 12's value is at least `ℓ` at every state of the exact `R(t_k)`, and line 13's at every state `R(t)` reaches at a time `t` of `τ_k`), and the bound arithmetic of lines 10-13 as theorems on bounds the caller supplies, [`SupportUpperCenter.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/SupportUpperCenter.lean) (`LinearSys.supportUpper_center_counterexample`: line 13 gives `−17/2` below the exact `ℓ = −8` for `ũ ∉ U`), [`TimePointBound.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/TimePointBound.lean) (`LinearSys.timePointBound`, lines 10-12), [`TimeIntervalBound.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/TimeIntervalBound.lean) (`LinearSys.timeIntervalBound`, line 13 over the first step), [`TimePointBoundOfInputReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/TimePointBoundOfInputReach.lean) (`timePointBoundOfInputReach`) — over any representation that multiplies by matrices and interval matrices and holds points: `ũ` is its `Recenter.center U` and `U₀` its `recenter` (`B = I_n`, `p = 0`), `P̂_U(Δt)` is `inputSolution` at `U₀` (Eq. 16), `C = F X₀ ⊕ G ũ` has `F`, `G` the tree's `correctionMatrix` and `constCorrectionMatrix` (Eq. 14-15) applied to `X₀` itself where [1] encloses it by `box(X₀)` for a representation that cannot multiply an interval matrix, and every support function is read from an oracle `ρ` bounding any set the representation is asked about. The remainder `E` of `F`, `G` and `P̂_U(Δt)` is the tree's norm bound `r·expRemainderBound` and not the entrywise `e^{\|A\|Δt} − Σ_{i≤η}(\|A\|Δt)^i/i!`; `η = m + 2`, Eq. (14) starting its sum at `i = 2` | `underspecified` — line 13's `ρ(P̂_U(t_{k+1}),ℓ)` bounds the particular solution at every time of `τ_k` only if `0 ∈ U₀`, that is `ũ ∈ U`: line 2's geometric center lies in a convex `U`, but the center of the enclosing interval, which Sec. 3 offers in its place, need not, and then line 13 falls below `ρ(R(τ_k),ℓ)`; `recenter U` is a set holding the origin by construction, which is what the proof uses; see Findings |
| `Alg. 1 (lower bounds)` | ("Reachability analysis using support functions", lines 1-10 and 14-16) With ũ ← B center(U) + p and U_0 ← B(U − center(U)) (line 2), P_u(Δt) = Tũ (Eq. 12) and P̌_U(Δt) = TU_0 (Eq. 17, line 4), d_{k+1} = (e^{AΔt})^⊤d_k (line 8), P_u(t_{k+1}) = e^{AΔt}P_u(t_k) + P_u(Δt) (line 9), ρ(H(t_{k+1}),ℓ) = ρ(X_0,d_{k+1}) + ρ(P_u(t_{k+1}),ℓ) (line 10) and ρ(P̌_U(t_{k+1}),ℓ) = ρ(P̌_U(t_k),ℓ) + ρ(P̌_U(Δt),d_k) (line 14), returns the lower bounds ρ(Ř(t_{k+1}),ℓ) = ρ(H(t_{k+1}),ℓ) + ρ(P̌_U(t_{k+1}),ℓ) (line 15) and ρ(Ř(τ_k),ℓ) = max{ρ(H(t_k),ℓ), ρ(H(t_{k+1}),ℓ)} + ρ(P̌_U(t_k),ℓ) (line 16) on the support functions of the time-point and time-interval reachable sets. | [`SupportLowerState.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/SupportLowerState.lean), [`SupportLower.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/SupportLower.lean) (`LinearSys.supportLower`, lines 1-4, 6-10 and 14-16, one `let` per line), [`SupportLowerMemImageReachSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/SupportLowerMemImageReachSet.lean) (`LinearSys.supportLower_mem_image_reachSet`: line 15's value is ℓ at a point of the exact R(t_k)), [`SupportLowerTimeIntervalLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/SupportLowerTimeIntervalLe.lean) (`LinearSys.supportLower_timeInterval_le`: line 16 is at most the larger of line 15 at t_k and at t_{k+1}, both in τ_k), [`HeldSimSupportCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HeldSimSupportCounterexample.lean), [`SupportLowerTimeInterval.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/SupportLowerTimeInterval.lean) (`LinearSys.supportLower_timeInterval_counterexample`: line 16 gives `3/2` above the exact `1` for `ũ ∉ U`), [`TimePointWitness.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/TimePointWitness.lean) (`LinearSys.timePointWitness`, line 15 from a witness on `inputReach`), [`TimeIntervalWitness.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/TimeIntervalWitness.lean) (`timeIntervalWitness`, a time point's witness for its step), and for discrete time [`ReachSetWitness.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ReachSetWitness.lean) (`LinearSysDT.reachSetWitness`) — `B = I_n`, `p = 0`, so ũ is a point `c` and U_0 = U − c; each ρ through a support vector, ρ(X_0,d) = d(ν(X_0,d)) and ρ(U_0,d) = d(ν(U,d)) − d(c) | `underspecified` — line 16 is a lower bound only when ũ ∈ U, that is 0 ∈ U_0: line 2's volumetric center lies in U, but the center of the enclosing interval, which Sec. 3 offers in its place, need not, and then line 16 can exceed ρ(R(τ_k),ℓ); see Findings |
| `Alg. 2` | "Verification algorithm (halfspace specifications)": for each row ℓ_i of the safe set's H, halves Δt and re-runs Alg. 1 until either the upper bound stays below f_(i) for every time interval — safe — or the lower bound exceeds it — unsafe; in case of a safety violation (Sec. 5.1) the support vector ν(Ř(t_k),ℓ_i), computed by evaluating Eq. (18) from the x(0) and the piecewise constant u(t) of Eqs. (19)-(20), is the counterexample. | [`VerifyHalfspace.lean`](../../src/CORALean/Specification/Operations/VerifyHalfspace.lean), [`VerifyHalfspaceSafe.lean`](../../src/CORALean/Specification/Theorems/VerifyHalfspaceSafe.lean), [`VerifyHalfspaceUnsafe.lean`](../../src/CORALean/Specification/Theorems/VerifyHalfspaceUnsafe.lean), [`ExistsRoundOfVerifyHalfspaceEqViolated.lean`](../../src/CORALean/Specification/Theorems/ExistsRoundOfVerifyHalfspaceEqViolated.lean), [`SupportCounterexampleViolates.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/SupportCounterexampleViolates.lean) (`LinearSys.supportCounterexample_violates`: once line 16 of `Alg. 1` exceeds f_(i), the run from `supportCounterexample` at t_k or t_{k+1} is a `IsTrajectory` whose state exceeds it), [`CounterexampleOfVerifyHalfspaceViolated.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/CounterexampleOfVerifyHalfspaceViolated.lean) (`LinearSys.counterexample_of_verifyHalfspace_violated`: `unsafe` on the lower bounds of `Alg. 1` names a round, a row i and a time t_j ∈ [0, t_end] at which that run, a `IsTrajectory` on [0, t_end], violates H_(i,·)x ≤ f_(i)) | `underspecified` — the falsification test is nested under the safety test and can never fire: it never returns unsafe; and when line 16's maximum is ρ(H(t_{k+1}),ℓ_i) the violating support vector is ν(Ř(t_{k+1}),ℓ_i), not ν(Ř(t_k),ℓ_i); see Findings |
| `Alg. 3 (exits)` | ("Verification algorithm (arbitrary convex unsafe sets)", lines 4-6 and 10-13) Runs the Gilbert-Johnson-Keerthi algorithm on R(t) ⊖ L using support functions: returns safe (R(t) ∩ L = ∅) when ρ(R̂(t),ℓ_i) + ρ(L,−ℓ_i) < 0 (lines 4-5); accumulates v̌_i = ν(Ř(t),ℓ_i) − ν(L,−ℓ_i) into P̌ ← conv(P̌, v̌_i) (lines 10-11) and returns unsafe (R(t) ∩ L ≠ ∅) when 0 ∈ P̌ (lines 12-13); the counterexample (Sec. 5.2) takes the weights λ_j of Σλ_jv_j = 0, Σλ_j = 1 over the vertices of the simplex P̌ and interpolates x(0) = Σλ_jx_j(0), u(k) = Σλ_ju_j(k) between the trajectories resulting in the vertices. | [`VerifyConvex.lean`](../../src/CORALean/Specification/Operations/VerifyConvex.lean) (`verifyConvex`, lines 4-5 and 12-13 folded over a caller-supplied direction sequence and a fuel bound), [`VerifyConvexStep.lean`](../../src/CORALean/Specification/Operations/VerifyConvexStep.lean) (`verifyConvexStep`, lines 4-13 for one direction), [`DiffPoint.lean`](../../src/CORALean/Specification/Operations/DiffPoint.lean) (`diffPoint`, line 10) and the answer type `VerifyAnswer`; soundness of `safe` in [`VerifyConvexSafe.lean`](../../src/CORALean/Specification/Theorems/VerifyConvexSafe.lean) (`holds_unsafeSet_of_verifyConvex_safe`) and of `violated` in [`Intersection.lean`](../../src/CORALean/Specification/Theorems/Intersection.lean) (`not_holds_unsafeSet_of_zero_mem_convexHull`) and [`VerifyConvexUnsafe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/VerifyConvexUnsafe.lean) (`LinearSys.not_holds_unsafeSet_of_verifyConvex_violated`, at the exact reachable set), with the loop invariant [`VerifyConvexFoldInv.lean`](../../src/CORALean/Specification/Theorems/VerifyConvexFoldInv.lean) (`verifyConvexFold_inv`); the counterexample in [`InterpolatedRunMem.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InterpolatedRunMem.lean) (`LinearSys.interpolated_run_mem`: the interpolated held-input run is a `IsTrajectory` whose state at t_k lies in L) — the bounds of lines 3-4 are hypotheses | `underspecified` — the λ_j have to be non-negative, which the linear system decides only when the simplex's vertices are affinely independent; see Findings |
| `Alg. 3 (search)` | ("Verification algorithm (arbitrary convex unsafe sets)", lines 1, 3, 7-9 and 14-25) Computes the bounds by Alg. 1 with Δt (line 3); sets falsifiable ← false when ρ(Ř(t),ℓ_i) + ρ(L,−ℓ_i) < 0 (lines 7-9); when falsifiable = false and 0 ∈ P̂, halves Δt and restarts (lines 14-16); otherwise chooses the next direction ℓ_{i+1}: the normal of the facet of P̌ closest to the origin once i > n+1 (lines 18-21, via the quadratic program min_{x∈P̌}‖x‖²), else a vector orthogonal to v̌_1,...,v̌_i by Gram-Schmidt pointing towards the origin (line 23). | [`VerifySearchState.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/VerifySearchState.lean), [`VerifySearchLoop.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/VerifySearchLoop.lean) (`LinearSys.verifySearchLoop`, lines 3, 7-9 and 14-25, one `let` per line, the exits of lines 4-6 and 12-13 where they stand), [`VerifySearch.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/VerifySearch.lean) (`LinearSys.verifySearch`, line 1 and the loop), [`VerifySearchLoopSound.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/VerifySearchLoopSound.lean) (`LinearSys.verifySearchLoop_sound`: from any state with `0 < Δt`, `kΔt = t`, a `Δt` small enough for `Alg. 1` and every vertex of `P̌` in `R(t) − L`, `safe` means `R(t) ∩ L = ∅` and `violated` means `R(t) ∩ L ≠ ∅`), [`VerifySearchSound.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/VerifySearchSound.lean) (`LinearSys.verifySearch_sound`, the same from line 1) — line 3 is `supportUpper` and `supportLower` at `Δt`, `k = t/Δt` steps, and ν(Ř(t),ℓ_i) the run of Eq. (18) from `supportCounterexample`; the support function and vectors of `L` and of the outer approximation, the test `0 ∈ P`, the facet of lines 19-20 (the quadratic program) and the Gram–Schmidt direction of line 23 are arguments, held only to what the exits read, so soundness holds for every search; `P̂` and `P̌` are the lists of their vertices; `fuel` bounds the loop and its answer is `undecided` when it runs out. The `Δt` halving doubles `k`, which is why the invariant `kΔt = t` survives line 15 | `underspecified` — line 18 sends `i ≤ n+1` to the Gram–Schmidt of line 23, but a non-degenerate `P̌` has `n+1` vertices, `i = n+1`, and there no direction is orthogonal to the vertices; `i ≥ n+1` is meant; see Findings |
| `Alg. 3 (termination)` | (Sec. 5.2) Since the computed upper and lower bounds converge to the exact value for Δt→0 and an increasing number of directions ℓ_i, Alg. 3 is guaranteed to always be able to either prove or disprove safety in decidable cases. | [`VerifySearchStall.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/VerifySearchStall.lean) — `verifySearch` (`Alg. 3 (search)`) at `ẋ = x + u`, `X₀ = {0}`, `U = [-1, 1]`, `t = 1` and every truncation order `η`, with every sound support function oracle, support vectors and hull test, and lines 19 and 23 returning the unit direction towards the origin, `+1`, from vertices all left of it. **Counterexample:** `LinearSys.verifySearch_stall_counterexample` | `false` — line 15 refines Δt only once `0 ∈ P̂`, but lines 19 and 23 choose the directions from `P̌`: with `L = {c}`, `c` between `e − 1` and the upper bound of `Alg. 1` at Δt = 1, `R(1)` keeps a distance `c − (e − 1) > 0` from `L`, and the search tries `ℓ = +1` forever without an exit or a refinement; see Findings |

## Findings

**`Alg. 2` can never return "unsafe".** Its two tests are nested — line 7 is
`if ρ(R̂(τ_k),ℓ_i) > f_(i) then verified ← false`, and line 9 the `else if
ρ(R̲(τ_k),ℓ_i) > f_(i) then return unsafe`. The second is reached only when the first
fails, that is when `ρ(R̂(τ_k),ℓ_i) ≤ f_(i)`; and `R̲` is an inner approximation of the
same set `R̂` encloses, so `ρ(R̲,ℓ) ≤ ρ(R,ℓ) ≤ ρ(R̂,ℓ) ≤ f_(i)` and line 9's condition
cannot hold. Line 10 is dead code, and the loop as printed is a semi-decision procedure
for safety alone. That contradicts the algorithm's own `Ensure` clause, "Safe ... or
unsafe", and the paper's prose that "Both algorithms also check for falsification and
return a counterexample in case of a safety violation". The repair is one line of
structure: the falsification test has to be reached whether or not the safety one fires. It is
tested first, before the safety test, in
[`VerifyHalfspace.lean`](../../src/CORALean/Specification/Operations/VerifyHalfspace.lean), which is
the reason its two soundness theorems both have reachable hypotheses. `Alg. 3` does not
share the defect: there the safety exit, the `falsifiable` flag and the intersection exit
are three separate tests.

**`Def. 4`.** The shape matrix is called positive semi-*definite*, but the set is written
with `Q^{-1}` and the support vector with `Qℓ/√(ℓ^T Qℓ)`, neither of which a singular `Q`
admits — and a degenerate ellipsoid, which semi-definiteness allows, is exactly that. Only
the support *function* `ℓ^T c + √(ℓ^T Qℓ)` survives there. CORALean stores a generator
matrix `G` with `Q = G G^T` for this reason, and
[`SupportBoundAttained.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/SupportBoundAttained.lean)
carries the branch the printed support vector cannot: where `G^T ℓ` vanishes the center
attains the value.

**`Sec. 4.2`: Eq. (20) aims the inputs in the wrong directions.** The counterexample
and the explicit inner approximation both rest on one claim: simulate Eq. (18),
`x(k+1) = e^{AΔt}x(k) + Tu(k)`, from `x(0) = ν(X_0,(e^{At_k})^⊤ℓ)` (Eq. 19) under
`u(j) = ν(U_0,(e^{At_j})^⊤ℓ) + ũ` (Eq. 20), and `x(k)` is the support vector `ν(Ř(t_k),ℓ)`.
Unrolled, Eq. (18) gives `x(k) = e^{At_k}x(0) + Σ_{j<k} e^{At_{k-1-j}}Tu(j)`, so `ℓ^⊤x(k)` is
largest when `u(j)` maximizes `ℓ^⊤e^{At_{k-1-j}}T u` over `U`, the direction
`(e^{At_{k-1-j}}T)^⊤ℓ`. Eq. (20) uses `(e^{At_j})^⊤ℓ`: `T` is missing, and the steps are
counted from the start instead of the end. Eq. (19) is right, and so is `Alg. 1`, whose
line 14 adds `ρ(P̌_U(Δt),d_j) = ρ(U_0,T^⊤d_j)`, `T` and all; only the simulation that is
supposed to attain it is wrong. It shows in one step, where the index plays no part:
`A = [[0,1],[0,0]]`, `Δt = 1`, `X_0 = {0}`, `U = [-1,1]²` (so `ũ = 0`), `T = I + A/2`, and
`ℓ = (1,-1/4)`. Eq. (20) picks `u(0) = ν(U,ℓ) = (1,-1)`, reaching `ℓ^⊤T(1,-1) = 3/4`; the
input `(1,1)` reaches `ℓ^⊤T(1,1) = 5/4`, which is `ρ(Ř(t_1),ℓ)`. With the safe set
`ℓ^⊤x ≤ 1`, a falsification test on the lower bound `5/4` fires, and the run returned as
the counterexample stays inside — `LinearSys.printedSupportInput_counterexample`. CORA's
`priv_verifyRA_supportFunc.m` does it right: it multiplies the input generators by `T`
(`underPU_G`) and reverses the input sequence (`fliplr`). `LinearSys.supportCounterexample`
uses the corrected direction, and `heldSim_le_supportCounterexample` proves that its
`x(k)` is then the support vector. The vertex polytope of the support vectors lies in
`R(t_k)` either way, since every input of `U` is admissible.

**`Alg. 1 (lower bounds)`: line 16 needs `ũ ∈ U`.** Line 16,
`ρ(Ř(τ_k),ℓ) = max{ρ(H(t_k),ℓ), ρ(H(t_{k+1}),ℓ)} + ρ(P̌_U(t_k),ℓ)`, pairs `H(t_{k+1})` with
`P̌_U(t_k)`, one step short. That is still a lower bound because
`ρ(P̌_U(t_{k+1}),ℓ) = ρ(P̌_U(t_k),ℓ) + ρ(TU_0,d_k)` and `ρ(TU_0,d_k) ≥ 0` when `0 ∈ U_0`, so
line 16 is at most line 15 at `t_k` or at `t_{k+1}` (`supportLower_timeInterval_le`), and
line 15 is a value the reachable set takes (`supportLower_mem_image_reachSet`; line 15
itself does not depend on `ũ` at all, the two `ũ` terms cancelling). `0 ∈ U_0` is
`center(U) ∈ U`, which line 2's volumetric center satisfies for a convex `U`. Sec. 3 offers
the center of the enclosing interval instead when the geometric center cannot be computed,
and that need not lie in `U`: for `A = 0`, `X_0 = {0}`, the simplex
`U = conv{0, e_1, e_2, e_3} ⊂ R³`, `ℓ = (1,1,1)` and `Δt = 1`, the box center is
`(1/2,1/2,1/2) ∉ U`, line 16 gives `ρ(Ř(τ_0),ℓ) = ℓ^⊤Tũ = 3/2`, while
`R(t) = tU` and `ρ(R(τ_0),ℓ) = 1`. A "lower bound" above the support function makes
`Alg. 2` (with its falsification test reachable) answer unsafe for a safe system. The
tree's theorems take `ũ ∈ U` as a hypothesis (`hc`). The example is
[`SupportLowerTimeInterval.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/SupportLowerTimeInterval.lean):
`LinearSys.supportLower_timeInterval_counterexample` shows `ũ ∉ U` with `ũ` the center of the box `[0,1]³`
enclosing `U`, line 16 at `k = 1` (`supportLower`) equal to `3/2`, and `1` the greatest value of `ℓ` on the exact
`R(t)`, `t ∈ [0,1]` (`reachSet_eq` at `A = 0`, so `R(t) = tU`), so `3/2 > 1`.

**`Alg. 2`: the counterexample can sit at `t_{k+1}`.** Sec. 5.1 names
`ν(Ř(t_k),ℓ_i)` as the counterexample once line 9 fires. Line 9 tests line 16's
time-interval bound, and when its maximum is `ρ(H(t_{k+1}),ℓ_i)`, `ρ(Ř(t_k),ℓ_i)` can stay
below `f_(i)` while `ρ(Ř(t_{k+1}),ℓ_i)` exceeds it; the counterexample is then the support
vector at `t_{k+1}`, still inside `τ_k`. `LinearSys.supportCounterexample_violates` returns
whichever of the two crosses, and `counterexample_of_verifyHalfspace_violated` lifts it to
`verifyHalfspace`'s answer: the run is a Carathéodory `IsTrajectory` on `[0, t_end]` from an
initial state of `X_0` under piecewise-constant inputs of `U`, and its state at that time
violates the row. CORA's implementation tests the time-point bounds, `affine_tp + underPU`,
which is the same repair.

**`Alg. 3 (exits)`: the interpolation weights have to be non-negative.** Sec. 5.2 takes
`λ_j` from `Σ_{j=1}^{n+1} λ_j v_j = 0`, `Σ λ_j = 1`. When the simplex's vertices are
affinely independent the solution is unique, and `0 ∈ P̌` makes it non-negative; when
they are not — `P̌` is degenerate, or the origin is reached with fewer than `n+1`
vertices, as line 12 allows — the system has other solutions, and a negative weight
extrapolates `x(0)` and `u(k)` out of `X_0` and `U`. Any non-negative weights certifying
`0 ∈ P̌` do; `LinearSys.interpolated_run_mem` takes them as a hypothesis and proves the
interpolated run a `IsTrajectory` whose state lies in `L`, by the linearity of Eq. (18) and
the convexity of `X_0`, `U` and `L`.

**`Alg. 1 (upper bounds)`: line 13 needs `ũ ∈ U`.** Line 13,
`ρ(R̂(τ_k),ℓ) = max{ρ(H(t_k),ℓ), ρ(H(t_{k+1}),ℓ)} + ρ(C,d_k) + ρ(P̂_U(t_{k+1}),ℓ)`, bounds the
particular solution at every time of `τ_k` by its value at `t_{k+1}`, which is the paper's own
`P(τ_k) ⊆ P(t_{k+1})`, true "if 0 ∈ U" (Sec. 4.1, citing the thesis's Prop. 3.3) and so when `0 ∈ U₀`. Line 2's `U₀ = B(U − center(U))` contains
the origin when `center(U)` is a point of `U`, as the geometric center of a convex `U` is; Sec. 3
offers the center of the enclosing interval when that cannot be computed, and that need not lie in
`U`. For `A = 0`, `X₀ = {0}`, `U = conv{c₀, c₀ + e₁, c₀ + e₂, c₀ + e₃}` with `c₀ = (−3,−3,−3)`,
`ℓ = (1,1,1)`, `Δt = 1` and `k = 1`: the interval center is `ũ = (−5/2,−5/2,−5/2) ∉ U`,
`ρ(U₀,ℓ) = −1/2`, `R(t) = tU` and `ρ(R(τ_1),ℓ) = −8`, while line 13 gives
`max{−15/2, −15} + 0 + 2·(−1/2) = −17/2 < −8`. A bound below the support function makes `Alg. 2`
verify an unsafe system. The tree's `supportUpper_outer` has no hypothesis on `ũ` because the
representation's `recenter` always holds the origin and `U − ũ ⊆ recenter U`: for the geometric center
it is the printed `U₀`, for any other center it is an enlargement of it. The example is
[`SupportUpperCenter.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/SupportUpperCenter.lean):
`LinearSys.supportUpper_center_counterexample` shows `ũ ∉ U` for `ũ` the center of the enclosing box, line 13 at `k = 1`
equal to `−17/2` (its `ρ(H(t_k),ℓ)` and `ρ(P̂_U(t_{k+1}),ℓ)` are `supportLower`'s, the same lines with the same `U₀`, and
`C = {0}` at `A = 0`), and a state of the exact `R(1)`, `1 ∈ τ_1`, with `ℓ = −8 > −17/2`. It is stated on the printed
formula and not on `supportUpper`, whose `recenter` holds the origin by construction.

**`Alg. 3 (search)`: line 18 is off by one.** Line 18 takes the facet branch only for `i > n+1`,
and sends `i ≤ n+1` to line 23, a direction "orthogonal to v̌_1,…,v̌_i" by Gram–Schmidt. The text
calls `P̌` "already non-degenerate" at `i > n+1`, but a polytope of `R^n` is non-degenerate from `n+1`
affinely independent vertices, `i = n+1`, and there the vertices span `R^n`, so no non-zero vector is
orthogonal to them and line 23 yields `ℓ_{i+1} = 0`. Read literally the same happens already at
`i = n` when the `n` vertices are linearly independent, the space meant being the one the
differences `v̌_j − v̌_1` span, whose orthogonal complement is a line. `i ≥ n+1` is the test that
sends a simplex to the facet branch of lines 19-21. The tree transcribes `i > n + 1`; its
soundness theorem does not depend on which direction the search takes.

**`Alg. 3 (termination)`: the search can stall at one Δt.** Line 15 halves Δt when
`falsifiable = false ∧ 0 ∈ P̂`, and Sec. 5.2 explains why: "Only if the polytope P̂ constructed
from the support vectors of the upper bound contains the origin, we definitely cannot disprove the
intersection using the current accuracy, and thus reduce the time step size." But the directions
come from `P̌` (lines 19 and 23), which nothing ties to `P̂`. Take `ẋ = x + u`, `X₀ = {0}`,
`U = [-1, 1]`, `t = 1`, so `R(1) ⊆ [−(e − 1), e − 1]`, and the truncation order `η` of `Alg. 1`
at Δt = 1, which makes the upper bound `ρ(R̂(1), +1)` at least `Σ_{i≤η} 1/(i+1)! + ε` with the
remainder `ε = (1/(η+1)!)(1 − 1/(η+2))⁻¹`; let `L = {c}` with `c = Σ_{i≤η} 1/(i+1)! + 1/(η+1)!`,
which exceeds `e − 1` by the exponential's Taylor bound and falls short of the upper bound since
`ε > 1/(η+1)!`. The sets are at distance `c − (e − 1) > 0`. The first direction is `ℓ₁ = +1`:
the safe test of line 4 fails because the upper bound exceeds `c`; the inner vertex `v̌₁`, a state
of `R(1)` minus `c`, is negative, and the outer vertex `v̂₁ = ν(R̂(1), +1) − c` is positive, so
neither `0 ∈ P̌` (line 12) nor `0 ∈ P̂` (line 14) holds. Every vertex of `P̌` being left of the
origin, the vector towards it (line 23) and the normal of the facet closest to it (line 19) are
`+1` again, and so is every later iteration: `LinearSys.verifySearch_stall_counterexample` shows
that `verifySearch` answers `undecided` for every `fuel` and every `η`, so for whichever `η` the
tuning of Sec. 5.1 picks from the system, which `L` does not enter. The convergence of the bounds
the claim rests on is not what fails: the search never gets to use it, as it never halves Δt.
The repair is the one Sec. 5.2 lists among its speed-ups, to choose the directions from `P̂` once
`falsifiable = false`; here the next direction would be `−1`, which puts the origin into `P̂` and
triggers the refinement. Lines 19 and 23 are read as GJK reads them, the unit direction towards
the origin; read literally, line 23 asks in `R¹` for a vector orthogonal to `v̌₁ ≠ 0`, which is
`0` (the off-by-one finding of `Alg. 3 (search)`).
