# Fully-Automated Verification of Linear Systems Using Inner- and Outer-Approximations of Reachable Sets

M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.

**Source:** https://arxiv.org/pdf/2209.09321v2 (arXiv v2, which matches the published IEEE TAC version — includes the "©2023 IEEE" notice; read via a custom PDF-content-stream text extractor, since poppler/pdftoppm is not installed in this environment so the Read tool's PDF-page mode is unavailable). NOTE: arXiv v1 (rendered fine by ar5iv/arxiv-html) has DIFFERENT Definition numbering — v1 has an extra "Definition 4 (Hyperball)" that v2 dropped, shifting v1's Def. 5-7 to v2's Def. 4-6. This file uses v2's (published) numbering, cross-checked directly against the v2 PDF text.  
**Inventory:** confirmed (full text of the 14-page body + 2 appendices read via the custom extractor)

Verifying a linear system with no parameters to tune, by computing an inner
approximation beside the outer one and stopping when they answer. `reachInner`
and `reachInnerReduced`, at both layers and both time domains.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Zonotope) Z := {c + Σ_{i=1}^γ G_(·,i) α_i \| α_i∈[-1,1]}, center c, generator matrix G; shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Def. 2` | (Constrained zonotope) CZ := {c + Σ G_(·,i) α_i \| Σ A_(·,i) α_i = b, α_i∈[-1,1]}, shorthand CZ=⟨c,G,A,b⟩_CZ; used to represent inner-approximations of reachable sets. | n/a — restated from Scott et al. 2016, which this formalization does not draw on directly |
| `Def. 3` | (Polytope) Halfspace representation P:={x \| Cx≤d}. | — |
| `Def. 4` | (Zonotope order reduction) reduce(Z,ρ_d) ⊇ Z returns an enclosing zonotope of order ≤ ρ_d. | — |
| `Def. 5` | (Hausdorff distance) For compact sets S1,S2⊆R^n, d_H(S1,S2) = max{ sup_{s1} inf_{s2} ‖s1-s2‖2, sup_{s2} inf_{s1} ‖s1-s2‖2 }. | — |
| `Def. 6` | (Reachable set) R(t) := {ξ(t;x(0),u(·)) \| x(0)∈X0, ∀θ∈[0,t]: u(θ)∈U}; also defines time-point R(t_k) and time-interval R(τ_k) reachable sets. | n/a — restated; tracked as `Def. 3.1` on [Althoff's thesis](2010-althoff-thesis.md) |
| `Alg. 1` | "Reachability algorithm (manual tuning)": baseline reachability algorithm for linear systems with a fixed, user-supplied time step Δt, truncation order η, and zonotope order ρ, returning the outer-approximation R̂([0,t_end]). | — |
| `Prop. 1` | (Affine dynamics error) Bounds the Hausdorff distance between the exact time-interval solution of the affine dynamics H(τ_k) and its outer-approximation. | — |
| `Prop. 2` | (Time-point error in particular solution) Bounds the Hausdorff distance between the exact particular solution P^U(t_{k+1}) and its recursively computed outer-approximation P̂^U(t_{k+1}). | — |
| `Prop. 3` | (Time-interval error in particular solution) Bounds the maximum Hausdorff distance over t∈τ_k between the exact time-interval particular solution P^U(t) and its outer-approximation. | — |
| `Prop. 4` | (Zonotope order reduction error) Bounds the Hausdorff distance introduced by iteratively reducing the particular solution's zonotope order, giving the recursion ε^r_{k+1} = ε^r_k + ε^r_k(ρ_k). | — |
| `Alg. 2` | "Reachability algorithm (automated tuning)": reachability algorithm that internally tunes the time step Δt_k and truncation order η_k given only an overall error bound ε_max. | — |
| `Thm. 1` | (Convergence) Alg. 2 terminates in finite time for arbitrary error bounds ε_max > 0 (proof uses Lemmas 1-4 from Appendix B: quadratic decrease of the accumulating error, at-least-linear decrease of the non-accumulating error). | — |
| `Prop. 5` | Given the error ε^x_k (eq. 31) of the reachable set R̂(τ_k), the corresponding output set Ŷ(τ_k) has error d_H(Y(τ_k),Ŷ(τ_k)) ≤ ε^y_k := ε^x_k·‖C‖. | — |
| `Prop. 6` | (Minkowski difference) Gives a constrained-zonotope formula for the Minkowski difference Z ⊖ P of a zonotope Z=⟨c,G⟩_Z and a vertex-represented polytope P=⟨v_1...v_s⟩_V. | — |
| `Prop. 7` | (Containment check) CZ ⊆ P (constrained zonotope in halfspace polytope) iff max(ν_1,...,ν_a) ≤ 0, where each ν_i is the optimum of a linear program (eq. 45). | — |
| `Prop. 8` | (Intersection check) Polytope P and constrained zonotope CZ intersect if ν=0 for a linear program ν = min over x,α,δ of δ subject to containment/constraint conditions. | — |
| `Alg. 3` | "Automated verification": combines Alg. 2's outer-approximation with an inner-approximation (via Prop. 6-8) to automatically prove or falsify a specification given by safe sets G_1..G_r and unsafe sets F_1..F_w. | — |
| `Prop. 9` | (Appendix A) Given the homogeneous solution H(t_k)=⟨c_h,G_h⟩_Z and particular solution P^u(t_k)=c_p, bounds the Hausdorff distance between the exact linear combination S = comb(H(t_k),H(t_{k+1})) and its zonotope outer-approximation. | — |
| `Prop. 10` | (Appendix A) For a compact set S⊂R^n and matrices M1,M2: d_H((M1+M2)S, M1 S) ≤ d_H(0, M2 S) — a general perturbation bound for linear maps of sets under the Hausdorff distance. | — |
| `Prop. 11` | (Appendix A) Bounds the Hausdorff distance between the propagated exact particular solution e^{At_k}P^U(t_k) and its outer-approximation. | — |
| `Lemma 1` | (Appendix B) The remainder of the exponential matrix E(Δt_k,η_k) (eq. 18) satisfies lim_{Δt_k→0} E = 0 and E ~ O(Δt_k^{η_k+1}). | — |
| `Lemma 2` | (Appendix B) The error ε^U_k(Δt_k,η_k) (eq. 25) satisfies lim_{Δt_k→0} ε^U_k = 0 and ε^U_k ~ O(Δt_k²). | — |
| `Lemma 3` | (Appendix B) The error ε^h_k(Δt_k,η_k) (eq. 23) satisfies lim_{Δt_k→0} ε^h_k = 0 and ε^h_k ~ O(Δt_k). | — |
| `Lemma 4` | (Appendix B) The error ε^{U,τ}_k(Δt_k,η_k) (eq. 26) satisfies lim_{Δt_k→0} ε^{U,τ}_k = 0 and ε^{U,τ}_k ~ O(Δt_k). | — |

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`StepInner.lean`](../src/CORALean/ContDynamics/LinearSys/StepInner.lean)
