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
construction. What the tree answers for is the two set representations the paper
defines for itself — polytopes in both forms and ellipsoids — and at the vertex list
and the ellipsoid alike the support function is an equality rather than a bound.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Support function) [cites [31, Sec. 2]] For compact convex S⊂R^n and ℓ∈R^n, ρ(S,ℓ) := max_{x∈S} ℓ^T x and the support vector ν(S,ℓ) := argmax_{x∈S} ℓ^T x, which need not be unique. | n/a — restated from Girard and Le Guernic 2008, which this formalization does not draw on directly | `restated` |
| `Def. 2` | (Zonotope) [cites [30, Def. 1]] Z := {c + Σ_{i=1}^γ G_(·,i) α_i \| α_i∈[-1,1]}, with ρ(Z,ℓ) = ℓ^T c + Σ_i \|ℓ^T G_(·,i)\| and ν(Z,ℓ) = c + Σ_i sgn(ℓ^T G_(·,i)) G_(·,i); shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Def. 3` | (Polytope) Halfspace representation P := {x \| Hx ≤ f} and vertex representation P := {Σ β_i v_i \| Σ β_i = 1, β_i ≥ 0}; for the vertex form the support function is max_i ℓ^T v_i and the support vector the maximizing vertex, for the halfspace form both come from a linear program. Shorthands ⟨H,f⟩_H and ⟨[v_1...v_s]⟩_V. | [`HPolytope.lean`](../../src/CORALean/ContSet/HPolytope/Real/HPolytope.lean), [`SupportBound.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/SupportBound.lean), [`VPolytope.lean`](../../src/CORALean/ContSet/VPolytope/Real/VPolytope.lean), [`SupportBound.lean`](../../src/CORALean/ContSet/VPolytope/Real/Operations/SupportBound.lean), [`SupportBoundAttained.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SupportBoundAttained.lean) — the vertex-form equality needs a nonempty vertex list | `correct` |
| `Def. 4` | (Ellipsoid) For a center c∈R^n and a positive semi-definite shape matrix Q, E := {x \| (x-c)^T Q^{-1} (x-c) ≤ 1}, with ρ(E,ℓ) = ℓ^T c + √(ℓ^T Qℓ) and ν(E,ℓ) = c + Qℓ/√(ℓ^T Qℓ); shorthand E=⟨c,Q⟩_E. | [`Ellipsoid.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Ellipsoid.lean), [`SupportBound.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Operations/SupportBound.lean), [`SupportBoundAttained.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/SupportBoundAttained.lean) | `underspecified` — `Q` is semi-definite but written through `Q⁻¹`, which a singular `Q` does not admit |
| `Def. 5` | (Reachable set) R(t) := {ξ(t,x(0),u(·)) \| x(0)∈X_0, ∀θ∈[0,t]: u(θ)∈U}, with R(t_k) the time-point and R(τ_k) the time-interval solution. | n/a — restated; tracked as `Def. 3.1` on [Althoff's thesis](../2010/althoff-thesis.md) | `restated` |
| `Problem 1` | (Verification) Given an LTI system with X_0, U and V, a safe set K=⟨H,f⟩_H and/or convex unsafe sets L_1..L_b, decide whether ∀t∈[0,t_end]: Y(t) ⊆ K and Y(t) ∩ ⋃_i L_i = ∅. | n/a — the task the paper's algorithms answer, not a claim to formalize | `not-a-claim` |
| `Alg. 1` | "Reachability analysis using support functions": for one direction ℓ, back-propagates the direction by (e^{AΔt})^T and propagates the particular solutions to return upper *and* lower bounds ρ(R̂(t_k),ℓ), ρ(R̲(t_k),ℓ), ρ(R̂(τ_k),ℓ), ρ(R̲(τ_k),ℓ) over the time horizon. | — partial: the bound arithmetic of lines 10-16, as theorems on bounds the caller supplies. [`TimePointBound.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimePointBound.lean) (`LinearSys.timePointBound`, lines 10-12, ρ(R(t_{k+1}),ℓ)), [`TimeIntervalBound.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimeIntervalBound.lean) (`LinearSys.timeIntervalBound`, line 13, ρ(R̂(τ_k),ℓ)), [`IntegralTimePointBound.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IntegralTimePointBound.lean) (`integralTimePointBound`) and [`IntegralTimeIntervalBound.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IntegralTimeIntervalBound.lean) (`integralTimeIntervalBound`), the same two over the exact integral reachable set, [`IntegralTimePointWitness.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IntegralTimePointWitness.lean) (`integralTimePointWitness`, line 15, the lower bound ρ(R̲(t_k),ℓ) with its attaining point), [`TimeIntervalWitness.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/TimeIntervalWitness.lean) (`timeIntervalWitness`, line 16) and [`IntegralTimeIntervalWitness.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IntegralTimeIntervalWitness.lean) (`integralTimeIntervalWitness`), and for discrete time [`ReachSetWitness.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/ReachSetWitness.lean) (`LinearSysDT.reachSetWitness`); missing: lines 1-9 and the loop itself, namely the back-propagation of ℓ by (e^{AΔt})ᵀ, the recursion computing P̂_U(t_{k+1}) and the curvature term C, the iteration over k and the returned bound sequences. The bounds on R₀, C and P̂_U are hypotheses of the declarations above and are not computed here | — |
| `Alg. 2` | "Verification algorithm (halfspace specifications)": for each row ℓ_i of the safe set's H, halves Δt and re-runs Alg. 1 until either the upper bound stays below f_(i) for every time interval — safe — or the lower bound exceeds it — unsafe. | [`VerifyHalfspace.lean`](../../src/CORALean/Specification/Operations/VerifyHalfspace.lean), [`VerifyHalfspaceSafe.lean`](../../src/CORALean/Specification/Theorems/VerifyHalfspaceSafe.lean), [`VerifyHalfspaceUnsafe.lean`](../../src/CORALean/Specification/Theorems/VerifyHalfspaceUnsafe.lean) | `underspecified` — the falsification test is nested under the safety test and can never fire: it never returns unsafe |
| `Alg. 3` | "Verification algorithm (arbitrary convex unsafe sets)": runs the Gilbert-Johnson-Keerthi algorithm on R(t) ⊖ L using support functions, building simplices from the support vectors of the outer and inner approximations, returning safe when a separating direction is found, unsafe when the inner simplex contains the origin, and halving Δt when neither settles it. | — partial: the two conclusive exits and their soundness. [`VerifyConvex.lean`](../../src/CORALean/Specification/Operations/VerifyConvex.lean) (`verifyConvex`, lines 4-5 and 12-13 folded over a caller-supplied direction sequence and a fuel bound), [`VerifyConvexStep.lean`](../../src/CORALean/Specification/Operations/VerifyConvexStep.lean) (`verifyConvexStep`, lines 4-13 for one direction), [`DiffPoint.lean`](../../src/CORALean/Specification/Operations/DiffPoint.lean) (`diffPoint`, line 10) and the answer type `VerifyAnswer`; soundness of `safe` in [`VerifyConvexSafe.lean`](../../src/CORALean/Specification/Theorems/VerifyConvexSafe.lean) (`holds_unsafeSet_of_verifyConvex_safe`) and of `violated` in [`Intersection.lean`](../../src/CORALean/Specification/Theorems/Intersection.lean) (`not_holds_unsafeSet_of_zero_mem_convexHull`) and [`VerifyConvexUnsafe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/VerifyConvexUnsafe.lean) (`LinearSys.not_holds_unsafeSet_of_verifyConvex_violated`), with the loop invariant [`VerifyConvexFoldInv.lean`](../../src/CORALean/Specification/Theorems/VerifyConvexFoldInv.lean) (`verifyConvexFold_inv`); missing: the direction search of lines 18-25 (the Gram-Schmidt step choosing the next direction from the simplex), the `falsifiable` flag and the Δt-halving restart of lines 7 and 14-16, and the calls to Alg. 1 for the bounds, which are hypotheses here. The direction sequence is the caller's, so no termination or completeness statement is made | — |

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
carries the branch the printed support vector cannot: where `G^T ℓ` vanishes the centre
attains the value.
