# Backward Reachability Analysis of Perturbed Continuous-Time Linear Systems Using Set Propagation

M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
Linear Systems Using Set Propagation". arXiv:2310.19083, 2023.

**Source:** https://mediatum.ub.tum.de/doc/1725668/document.pdf — Wetzlinger's thesis, Appendix A.4 (pp. 92–108), a verbatim reprint of arXiv v1 (29 Oct 2023), read with `pypdf`; cross-read against https://arxiv.org/html/2310.19083v3. NOTE: the numbering below is v1's, as reprinted in the thesis. arXiv v3 (18 Sep 2025) inserts a polytope-to-constrained-zonotope conversion as its `Alg. 1`, so v1's `Alg. 1` and `Alg. 2` are v3's `Alg. 2` and `Alg. 3`; it also renames the minimal and maximal backward reachable sets to AE and EA. Every Definition, Proposition, Lemma and Theorem keeps its number. The paper has since appeared as M. Wetzlinger and M. Althoff, IEEE Transactions on Automatic Control, vol. 71, pp. 352–367, 2026, doi:10.1109/TAC.2025.3592719.  
**Inventory:** confirmed

Backward reachability for linear systems by set propagation rather than
Hamilton-Jacobi gridding, which is what makes it polynomial in the state
dimension: four algorithms, for the time-point and time-interval solutions of the
minimal set (all inputs, some disturbance — what a system cannot avoid) and of the
maximal set (some input, all disturbances — what it can steer into). CORA's
`reachBackward` and its `priv_reach_backward_{AE,EA}_{timepoint,timeinterval}`
are exactly these four; they cite the work under the working title "Backward
Reachability Analysis with State Constraints for Linear Systems using Set
Propagation", which is not a separate publication — no such title exists on arXiv
or in Crossref, and the AE/EA naming CORA uses is this paper's own from v2 onward.
CORALean has no backward reachability at all yet, so every row below is open.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Support function) [cites [2, Sec. 2]] For compact S⊂R^n and ℓ∈R^n, ρ(S,ℓ) := max_{s∈S} ℓ^T s. | n/a — restated from Girard and Le Guernic 2008, which this formalization does not draw on directly |
| `Def. 2` | (Polytope) [cites [5, Sec. 1.1]] Halfspace representation P := {s∈R^n \| Hs ≤ d} with H∈R^{h×n}, d∈R^h; shorthand P=⟨H,d⟩_H. | n/a — restated from Ziegler's *Lectures on Polytopes*, which this formalization does not draw on directly |
| `Def. 3` | (Zonotope) [cites [8, Def. 1]] Z := {c + Σ_{i=1}^γ G_(·,i) α_i \| α_i∈[-1,1]}; shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Def. 4` | (Constrained zonotope) [cites [12, Def. 3]] CZ := {c + Σ G_(·,i) α_i \| Σ K_(·,i) α_i = l, α_i∈[-1,1]}; shorthand CZ=⟨c,G,K,l⟩_CZ. | n/a — restated from Scott et al. 2016, which this formalization does not draw on directly |
| `Def. 5` | (Forward reachable set) R(t) := {ξ(t;x_0,u(·)) \| x_0∈X_0, ∀θ∈[0,t]: u(θ)∈U} for ẋ = Ax + u. | n/a — restated; tracked as `Def. 3.1` on [Althoff's thesis](../2010/althoff-thesis.md) |
| `Def. 6` | (Minimal backward reachable set) [cites [17, Def. 2 and Def. 4]] R^∀∃(-t) := {x_0 \| ∀u(·)∈U ∃w(·)∈W: ξ(t;x_0,u(·),w(·))∈X_end} — the states that cannot avoid the target — and its time-interval version, which requires the state to pass through X_end at some t∈τ. | — |
| `Def. 7` | (Maximal backward reachable set) [cites [17, Def. 1 and Def. 3]] R^∃∀(-t) := {x_0 \| ∃u(·)∈U ∀w(·)∈W: ξ(t;x_0,u(·),w(·))∈X_end} — the states that can be steered into the target despite any disturbance — and its time-interval version. | — |
| `Prop. 1` | (Convergence of particular solution) The outer approximation (23) and the inner approximation (24) of the particular solution Z_S, propagated by (25), both converge to the exact particular solution Z_S(t) = {∫_0^t e^{A(t-θ)}s(θ)dθ \| s(θ)∈S} as Δt→0. | — |
| `Prop. 2` | (Union) [cites [1, Prop. 2]] ⋃_{t∈τ} R^∀∃(-t) ⊆ R^∀∃(-τ) and ⋃_{t∈τ} R^∃∀(-t) ⊆ R^∃∀(-τ); the proof is the order of the quantifiers. | n/a — restated from Mitchell 2007, which this formalization does not draw on directly |
| `Assumption 1` | (Fixed parameters) The truncation order η in (23), the number of propagation steps ω, and the number h of halfspaces constraining X_end are fixed. | n/a — a standing hypothesis for the runtime-complexity analysis, not a claim to formalize |
| `Def. 8` | (Viability/Discriminating kernel) [cites [47, Def. 6], [48, Def. 2]] D(τ,K) := {x_0∈K \| ∀w(·)∈W ∃u(·)∈U ∀t∈τ: ξ(t;x_0,u(·),w(·))∈K}; dropping w(·) gives the viability kernel V(K). | n/a — restated from Kaynama et al. (2011, 2015) in the related-work section, which this formalization does not draw on directly |
| `Prop. 3` | (Minimal time-point backward reachable set) R^∀∃(-t) = e^{-At}((X_end ⊕ -Z_W(t)) ⊖ Z_U(t)), independently of the set representations chosen; a continuization of the discrete-time case of [38, Thm. 2.4]. | — |
| `Prop. 4` | (Outer approximation of Minkowski sum) For a polytope P=⟨H,d⟩_H with h constraints and a zonotope Z, P ⊕ Z ⊆ P ⊕̂ Z := ⟨H, d+d̃⟩_H with d̃_(j) = ρ(Z, H^T_(j,·)), at complexity O(hnγ). | — |
| `Thm. 1` | (Time-interval minimal backward reachable set) With Û⊂U a set of q input trajectories, R^∀∃(-τ) is outer approximated by the union over the ω steps of R̂^∃(-τ_k;u_0(·)) ∩ ⟨N,p⟩_H, where u_0 is the center input trajectory, N's rows are the q directions ℓ_j, and p_(j) = min_i ρ(R̂^∃(-τ;u_i(·)), ℓ_j). | — |
| `Alg. 1` | "Minimal time-interval backward reachable set": propagates the disturbance particular solution and the convex hull of the converted target set over ω steps, carries the support functions of the q input trajectories alongside, and intersects the constructed polytope with R̂^∃(-τ) to return R̂^∀∃(-τ). | — |
| `Prop. 5` | (Maximal time-point backward reachable set) R^∃∀(-t) = e^{-At}((X_end ⊖ Z_W(t)) ⊕ -Z_U(t)), independently of the set representations chosen; a continuization of the discrete-time case of [38, Thm. 2.4]. | — |
| `Lemma 1` | (Distributivity of Minkowski difference over convex hull) For compact, convex, non-empty S1,S2,S3⊂R^n: conv(S1 ⊖ S3, S2 ⊖ S3) ⊆ conv(S1,S2) ⊖ S3. | — |
| `Thm. 2` | (Time-interval maximal backward reachable set) The union ⋃_{t∈τ_k} R^∃∀(-t) is inner approximated by e^{-At_{k+1}}(-Z̲_U(t_k) ⊕ conv(CZ(X_end ⊖ F box(X_end) ⊖ B_µ ⊖ Ẑ_W(τ_k)), CZ(e^{AΔt}X_end ⊖ F box(X_end) ⊖ B_µ ⊖ Ẑ_W(τ_k)))), and the union over all ω steps inner approximates R^∃∀(-τ). | — |
| `Alg. 2` | "Maximal time-interval backward reachable set": pre-computes the input and disturbance particular solutions up to t_0 and the two polytopes P1, P2 of the inner-approximated homogeneous time-interval solution, then implements Thm. 2 step by step and returns the union. | — |

