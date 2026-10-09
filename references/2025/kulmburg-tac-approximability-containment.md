# Approximability of the Containment Problem for Zonotopes and Ellipsotopes

A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025. doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.

**Source:** https://arxiv.org/pdf/2404.11185v4 (arXiv v4, 30 Jul 2025, "accepted for publication in the IEEE Transactions on Automatic Control", 16 pages including the Appendix, read in full; text extracted with `pypdf`, the proof of Lemma 26 and the application equations (53)-(57) read from the page images). The typeset IEEE article was not reachable; volume and pages are not given. CORA cites it in `@ellipsoid/contains_.m` and `@ellipsoid/private/priv_containsEllipsoid.m` ("Approximability of the Containment Problem for Zonotopes and Ellipsotopes") and, as "Hardness and Approximability of the Containment Problem for Zonotopes and Ellipsotopes (to appear)", in `@zonotope/contains_.m`, without a result number. Numbering is v4's.  
**Inventory:** confirmed (against v4: Definitions 1-3, 5, 8-9 and 23, Propositions 7 and 28, Theorems 12-13, 15-17, 19, 21 and 24, Lemmas 14, 25-27, Remarks 4, 6, 10-11, 20 and 22 and Example 18, each with its own counter, the claims in Secs. III-A, IV and V, and the equations below, which are the numbered displays that make a claim)

The containment problem for ellipsotopes `E_p(G, c) = {c + Gα | ‖α‖_p ≤ 1}` read as a matrix-norm
problem: `r(Ê, E)`, the smallest scaling of the circumbody that contains the inbody, is a
generalized matrix norm (`Thm. 12`, dual form `Eq. 21`), and the linear relaxation of Sadraddini
and Tedrake (`Eq. 28`) generalizes to ellipsotope circumbodies with an accuracy bound
(`Thm. 15`), exact where the dual optimizer has columns equal up to sign (`Thm. 16`);
semidefinite relaxations cover `p = q = 2` (`Thm. 13`) and `q ∈ (1, 2]` (`Thm. 17`, `Thm. 19`).
Hardness: most `(p, q)` are inapproximable unless P = NP (`Sec. IV`), and the case the paper
adds, an ellipsotope in a zonotope, is not in FPTAS (`Thm. 21`, `Thm. 24`), by reduction from
the `p ↦ 1` matrix norm through a gadget of radii `L`, `ϱ` (`Lemma 25`-`Lemma 27`,
`Prop. 28`). Section V uses the relaxation to compute safe sets of a linear system by one
conic program. Formalized here: the ellipsotope norm (`Prop. 7`), the centre shift of
`Lemma 14`, the containment half of `Thm. 15` and its use in `Eq. 53`, the row constraints
`Eq. 55`-`Eq. 57` and the gadget's radii (`Lemma 26`). The semidefinite and hardness results
are open: Gaussian moments, semidefinite programs and NP-hardness have no counterpart in the
tree.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 2` | For compact, convex Ŝ and S centrally symmetric about c_S, r(Ŝ, S) = max_{s ∈ Ŝ} ‖s - c_S‖_S, r the smallest scaling with Ŝ ⊆ r(S - c_S) + c_S (Eq. 1). | n/a — restated; the zonotope case is `Eq. 18` on [Kulmburg and Althoff 2021](../2021/kulmburg-ejc-zonotope-containment.md), the ellipsotope case `Thm. 12` below | `restated` |
| `Def. 1` | (L_{p,q}-norms and L⊤_{p,q}-norms) ‖A‖_{L_{p,q}} is the q-norm of the vector of the columns' p-norms; ‖A‖_{L⊤_{p,q}} = ‖Aᵀ‖_{L_{p,q}} (Eq. 3-5). | n/a — a definition; [`ZonotopeSubsetEllipsotopeOfLR.lean`](../../src/CORALean/Global/ZonotopeSubsetEllipsotopeOfLR.lean) writes ‖X‖_{L⊤_{1,q}} out as the q-norm of the rows' absolute sums | `not-a-claim` |
| `Def. 2` | (Operator matrix p ↦ q-norm) ‖A‖_{p↦q} = sup_{‖v‖_p ≤ 1} ‖Av‖_q (Eq. 6). | n/a — a definition | `not-a-claim` |
| `Eq. 7` | ‖A‖₁ = ‖A‖_{L_{1,∞}} and ‖A‖_∞ = ‖A‖_{L⊤_{1,∞}}: the operator 1- and ∞-norms are the maximal absolute column and row sums. | n/a — restated from Horn and Johnson [11, Chapter 5.6] | `restated` |
| `Eq. 8` | (Dual norm) ‖y‖* = sup_{‖x‖ ≤ 1} yᵀx. | n/a — a definition | `not-a-claim` |
| `Eq. 9` | ‖x‖*_p = ‖x‖_{p*}, p* the Hölder conjugate. | n/a — restated from Boyd and Vandenberghe [13, A.1.6] | `restated` |
| `Eq. 10` | (Dual matrix norm) ‖Y‖* = sup_{‖X‖ ≤ 1} tr(XᵀY). | n/a — a definition | `not-a-claim` |
| `Def. 3` | (Polyhedra and polytopes) P(Λ, λ) = {x \| Λx ≤ λ}; a bounded one is a polytope, the convex hull of its vertices; symmetric if x ∈ P ⇔ -x ∈ P. | n/a — textbook definitions | `not-a-claim` |
| `Remark 4` | A symmetric V-polytope is {Vα \| ‖α‖₁ ≤ 1}, the columns of V its vertices. | n/a — a remark on a representation | `not-a-claim` |
| `Def. 5` | (Ellipsotopes) E_p(G, c) = {c + Gα \| ‖α‖_p ≤ 1}, non-degenerate if G has full rank and n ≤ m; p = 2 ellipsoids, p = ∞ zonotopes (Eq. 12). | n/a — restated from Kousik et al., "Ellipsotopes", Def. 2 | `restated` |
| `Remark 6` | Ellipsotope means basic ellipsotope here. | n/a — a remark on terminology | `not-a-claim` |
| `Prop. 7` | (Ellipsotope norm) For m ≥ n and G of full rank, x ↦ min_{Gα=x} ‖α‖_p is a norm on ℝⁿ for every p ∈ [1, ∞], whose unit ball coincides with E_p(G). | [`CoeffNormBallEq.lean`](../../src/CORALean/Global/CoeffNormBallEq.lean) — over any norm on the coefficients, `p`-norms among them: the norm laws, the unit ball E_p(G) and its boundary the unit sphere | `correct` |
| `Def. 8` | (Approximation algorithms) A τ-approximation algorithm gives opt ≤ approx ≤ τ opt in time polynomial in the input size (Eq. 14). | n/a — a definition | `not-a-claim` |
| `Def. 9` | (PTAS, FPTAS, inapproximability) The classes of problems with a (1 + ε)- resp. (1 - ε)-approximation for every ε, polynomial in 1/ε for FPTAS; τ-inapproximable and inapproximable. | n/a — a definition | `not-a-claim` |
| `Remark 10` | Linear, convex quadratic and many semidefinite programs are in FPTAS by interior-point methods, with the operation counts O(n^3.5 ln n) and O(m^4.5 ln m) for fixed accuracy. | n/a — a remark on solvers, running times | `not-a-claim` |
| `Remark 11` | Inapproximability within a factor Ω(N²) generalizes to τ a function of the input size. | n/a — a remark extending a definition | `not-a-claim` |
| `Thm. 12` | r(Ê, E) = max_{‖α‖_p ≤ 1} min_{Hβ = Gα + c - d} ‖β‖_q is the smallest scalar with Ê ⊆ r(E - d) + d, and r ≤ 1 iff Ê ⊆ E; for a degenerate E with rank [G, c - d, H] ≠ rank H, r = ∞ by convention (Eq. 15-16). | — partial: [`EllipsotopeSubsetIff.lean`](../../src/CORALean/Global/EllipsotopeSubsetIff.lean) (the maximum is attained and r ≤ 1 iff Ê ⊆ E, at a surjective H); missing: that r is the smallest scaling, and the degenerate circumbody with its convention and the projection reduction (Eq. 19-20) | — |
| `Sec. III-A` | (Symmetric V-polytope in ellipsotope) The circumbody norm is convex in α, so by the Bauer maximum principle its maximum is attained at α = ±eᵢ: 2m convex problems, in FPTAS. | n/a — the Bauer maximum principle and a complexity class, argued in the paragraph; the zonotope case of the principle is `Sec. III` on [Kulmburg et al. 2024](../2024/kulmburg-ecc-zonotope-ellipsotope-containment.md) | `not-a-claim` |
| `Thm. 13` | (Ellipsoid in ellipsoid) For non-degenerate E, r(Ê, E) = √(min_{ρ ∈ S} ρ), S the set of ρ with the linear matrix inequality (23) for some δ ≥ 0, Θ = H⁺G, θ = H⁺(c - d). | — | — |
| `Thm. 13 (complexity)` | The semidefinite program (22) takes O((m + 1)^4.5 ln(m + 1)) operations: the problem is in FPTAS. | n/a — a running time | `not-a-claim` |
| `Lemma 14` | For Ẑ = Z(G, c) and Ê = E_q(H, d), r(Ẑ, Ê) = r(Z(G'), E_q(H)), G' = [G, c - d] (Eq. 25). | [`EllipsotopeCentreShift.lean`](../../src/CORALean/Global/EllipsotopeCentreShift.lean) — the maximum over the cube of G' and the one over the cube of G at the shifted centre are the same numbers; circumbody norm any `coeffNorm` of a surjective map | `underspecified` — the proof takes r through the ellipsotope norm (`Prop. 7`), which needs the circumbody non-degenerate (H onto), as the formalization assumes; the degenerate case is `Thm. 12`'s convention |
| `Eq. 21` | For non-degenerate Ê, r(Ê, E) = max_{‖Hᵀx‖_{q*} ≤ 1} ‖Gᵀx‖_{p*} + xᵀ(c - d). | n/a — restated from Kulmburg, "The Generalized Matrix Norm Problem", [22, Cor. 3.2]; tracked as `Eq. 7` on [Kulmburg et al. 2024](../2024/kulmburg-ecc-zonotope-ellipsotope-containment.md) | `restated` |
| `Eq. 28` | For zonotopes, LR_∞(G, H) = min_{HX = G} ‖X‖_∞ (Eq. 27) satisfies r(Ẑ, Z) ≤ LR_∞(G, H): LR_∞ ≤ 1 implies Z(G) ⊆ Z(H). | n/a — restated from Sadraddini and Tedrake [8, Cor. 4]; tracked as `Thm. 3` on [Sadraddini and Tedrake 2019](../2019/sadraddini-cdc-polytope-containment.md) | `restated` |
| `Thm. 15` | For H surjective, LR_q(G, H) = min_{HX = G} ‖X‖_{L⊤_{1,q}} satisfies r(Z(G), E_q(H)) ≤ LR_q ≤ (γ_{q*} √m / γ_1) r(Z(G), E_q(H)), γ_k the k-th root of the k-th moment of a standard normal (Eq. 29-31); so LR_q ≤ 1 implies Z(G) ⊆ E_q(H), and LR_q > γ_{q*}√m/γ_1 implies Z(G) ⊄ E_q(H). | — partial: [`ZonotopeSubsetEllipsotopeOfLR.lean`](../../src/CORALean/Global/ZonotopeSubsetEllipsotopeOfLR.lean) (a matrix X with HX = G and ‖X‖_{L⊤_{1,q}} ≤ 1 gives Z(G) ⊆ E_q(H), for any q ∈ [1, ∞]); missing: that LR_q is a minimum and bounds r from above (the first inequality of Eq. 30), and the accuracy bound with the Gaussian moments, from [22, Thm. 5.9], with the non-containment half | — |
| `Thm. 15 (complexity)` | LR_q is computed in O((ml)^3.5 ln(ml)) operations: by linear programming for q = 1, ∞, convex quadratic optimization for q = 2. | n/a — a running time | `not-a-claim` |
| `Eq. 32` | LR_q(G, H) = max_{‖HᵀY‖_{L⊤_{∞,q*}} ≤ 1} tr(GᵀY), solvable in O((mn)^3.5 ln(mn)) operations. | n/a — restated from [22, Prop. 3.1, Lemma 2.3] | `restated` |
| `Thm. 16` | For Y a maximizer of Eq. 32, if its columns are equal up to sign then LR_q(G, H) = r(Z(G), E_q(H)); in particular for q = ∞ and H square and invertible (a parallelotope) the condition always holds. | — | — |
| `Thm. 17` | For H surjective and q ∈ (1, 2], ZSR_q(G, H) = ½ min_{(v,w) ∈ K} (‖v‖₁ + ‖w‖_{q/(2-q)}), K the tuples with the matrix inequality (39), satisfies r(Z(G), E_q(H)) ≤ ZSR_q ≤ (γ_{q*}/γ_1) r(Z(G), E_q(H)) (Eq. 38-40). | — | — |
| `Thm. 17 (complexity)` | ZSR_q is computed in O(n^4.5 ln n) operations by a semidefinite solver. | n/a — a running time | `not-a-claim` |
| `Example 18` | The unit disk Ê = E(I₂) and an eight-generator zonotope: r̂ = ZSR₂(G, I₂) ≈ 3.89, r(Ẑ, Ê) ≈ 3.67, √(2/π) r̂ ≤ r ≤ r̂ (Fig. 1). | n/a — a numerical example | `not-a-claim` |
| `Thm. 19` | For Ê = E_p(G), E = E_q(H), 1 < q ≤ 2 ≤ p < ∞ and H surjective, SR_{p,q}(G, H) = ½ min_{(v,w) ∈ K} (‖v‖_{p/(p-2)} + ‖w‖_{q*/(q*-2)}) satisfies r(Ê, E) ≤ SR_{p,q} ≤ γ_{q*} γ_p r(Ê, E) (Eq. 41-43). | — | — |
| `Thm. 19 (complexity)` | SR_{p,q} is computed in O(n^4.5 ln n) operations by a semidefinite solver. | n/a — a running time | `not-a-claim` |
| `Eq. 44` | For s < t and x ∈ ℝⁿ, ‖x‖_t ≤ ‖x‖_s ≤ n^{1/s - 1/t} ‖x‖_t. | n/a — restated from [27, Prop. 37.6] | `restated` |
| `Sec. IV` | The hardness read off the literature: (1) in FPTAS for p = 1 or p = q = 2; (2) τ-inapproximable unless P = NP for 1 ≤ q ≤ 2 ≤ p ≤ ∞, q ≠ p; (3) inapproximable unless P = NP for p = ∞ and 2 < q < ∞; (4) for 1 < p < 2 and q = 1; (5) for p = q ∈ (1, 2) or (2, ∞); (6) for 1 < p < 2 and q ≤ p, or q ≤ p and 2 < q < ∞; (7) inapproximable unless NP ⊆ BPP for q ≥ p and 1 < q < 2, or 2 < p < ∞ and q ≥ p; (8) for other cases with q < ∞ only the 2 ↦ 4 norm, inapproximable assuming the Exponential Time Hypothesis. | n/a — restated from the hardness of the p ↦ q matrix norm: [28, Thm. 1.1, 1.4, 6.4], [29, Thm. 6.2-6.4], [30, Thm. 2.5] | `restated` |
| `Remark 20` | For some of these cases stronger statements hold, as Ω(2^{(log N)^{1-δ}})-inapproximability for p = q ∈ (1, 2) unless NP ⊆ DTIME(2^{polylog N}) [29, Thm. 6.2]. | n/a — a remark on the literature | `not-a-claim` |
| `Thm. 21` | Unless P = NP, the ellipsotope-in-zonotope containment problem for p-ellipsotopes, p ∈ (1, ∞], is not in FPTAS, and the decision form is co-NP-hard, also with equal centres. | — | — |
| `Remark 22` | The reduction of `Thm. 21` uses a circumbody zonotope of order below 2, so the problem is not in FPTAS even at order 2. | n/a — a remark on the proof | `not-a-claim` |
| `Def. 23` | (RP and RQP) Randomized polynomial and quasi-polynomial time, one-sided error with probability at least 1/2. | n/a — a definition | `not-a-claim` |
| `Thm. 24` | Unless NP = RP, the ellipsotope-in-zonotope containment problem for p ∈ (2, ∞] is inapproximable, and inapproximable within Ω(2^{(log Ñ)^{1-δ}}) for every δ > 0 unless NP ⊆ RQP, also with equal centres. | — | — |
| `Sec. V` | The safe set of a sampled-data linear system as one conic program: the terminal region T as zonotope or ellipsoid, the containment R_x(t_end; T̂) ⊆ T by `Thm. 15` (Eq. 45-54, 58), solved in O(M^3.5 ln M) operations, and the 2k-dimensional platoon benchmark against the terminal set approach (Eq. 59-61, Tables I-III, Fig. 3). | n/a — a modelling section with running times and experiments | `not-a-claim` |
| `Eq. 53` | R_x(t_end; T̂) ⊆ T = E_q(H Diag(s), c_T) holds if some Z has ‖Z‖_{L⊤_{1,q}} ≤ 1 and H Diag(s) Z = [G_{Nts}, c_{Nts} - c_T], R_x(t_end; T̂) ⊆ Z(G_{Nts}, c_{Nts}). | [`ZonotopeSubsetEllipsotopeOfLRCentre.lean`](../../src/CORALean/Global/ZonotopeSubsetEllipsotopeOfLRCentre.lean) — Z(G, c) ⊆ E_q(H, d) for any linear H, G, any centres | `correct` |
| `Eq. 55` | At q = ∞, ‖Diag(s)⁻¹ Z'‖_{L⊤_{1,q}} ≤ 1 is equivalent to ‖ζ'_j‖₁ ≤ s_j for every row ζ'_j of Z'. | [`TerminalSetRowConstraints.lean`](../../src/CORALean/Global/TerminalSetRowConstraints.lean) — s_j > 0 | `correct` |
| `Eq. 56` | At q = 2, ‖Diag(s)⁻¹ Z'‖_{L⊤_{1,q}} ≤ 1 is equivalent to Σ_j ‖ζ'_j‖₁² / s_j² ≤ 1, not a convex constraint. | [`TerminalSetRowConstraints.lean`](../../src/CORALean/Global/TerminalSetRowConstraints.lean) — s_j > 0 | `correct` |
| `Eq. 57` | The stronger ‖ζ_j‖₁ ≤ s_j / √m for every j ∈ {1, …, m} implies Eq. 56, and is linear. | [`TerminalSetRowConstraints.lean`](../../src/CORALean/Global/TerminalSetRowConstraints.lean) — also at m = 0 | `correct` |
| `Eq. 63` | The gadget: H = [[I_n, -I_n], [1ᵀ, 1ᵀ]] ∈ ℝ^{(n+1)×2n} (Eq. 62) and the circumbody Ẑ = {Hβ \| ‖β‖_∞ ≤ 1, β ≥ 0}. | n/a — a definition of the reduction's instance | `not-a-claim` |
| `Lemma 25` | Ẑ = Z(½H, n e_{n+1}), and for ρ ∈ [0, 1], {x \| x_{n+1} = ρ} ∩ Ẑ = (ρB₁) × {ρ}; moreover B₁ × [1, 2n - 1] ⊂ Ẑ (Eq. 64). | — | — |
| `Lemma 26` | For n ∈ ℕ∖{1} and p ∈ (1, ∞) there are L ∈ (n - 1, n) and ϱ ∈ (0, 1) with 1 - ϱᵖ = ((n - ϱ)/L)ᵖ (Eq. 66) and L = (1 - ((n - ϱ)/L)ᵖ)^{1/p-1} ((n - ϱ)/L)^{p-1} (Eq. 67); for p = ∞, L = n - 1, ϱ = 1. | [`ExistsGadgetRadii.lean`](../../src/CORALean/Global/ExistsGadgetRadii.lean) — n ≥ 2, p ∈ (1, ∞), with the paper's ϱ = n^{-1/(p-1)} and L = (n - ϱ)/(1 - ϱᵖ)^{1/p}, both bounds strict | `underspecified` — n = 0 is not excluded, where no such L exists (the setting has n > 1, Eq. 62); the proof ends at L ≥ n - 1 for an open bound and equates Eq. 70 with 2 · 1/2ᵖ ≤ n for 2^{1-1/p} ≤ n; see Findings |
| `Lemma 27` | For p ∈ (1, ∞], A ∈ ℝ^{n×m} and G_A, H of Eq. 65 and Eq. 62, r(E_p(G_A), Z(H)) = 1 iff ‖A‖_{p↦1} = 1, and likewise with < or >. | — | — |
| `Prop. 28` | For A ≠ 0, σ(ξ) = r(E_p(G_{A/ξ}), Z(H)) is continuous, tends to ∞ as ξ → 0, σ(ξ̂) ≤ 1 for ξ̂ = m^{(p-1)/p} ‖A‖_{1↦1}, has the unique solution σ(ξ) = 1 at ξ = ‖A‖_{p↦1}, and \|σ(ξ') - σ(ξ)\| ≥ (‖A‖_{1↦∞}/ξ̂²) \|ξ - ξ'\| on (0, ξ̂] (Eq. 78-80). | — | — |

## Findings

**`Lemma 14` — a non-degenerate circumbody.** The statement has no hypothesis on H, and its
proof rewrites r through the ellipsotope norm of `Prop. 7`, which is defined only when H has
full row rank (every point is some Hβ). For a degenerate circumbody `Thm. 12` fixes r = ∞
when the inbody leaves its affine span and otherwise projects; the identity is read at the
non-degenerate circumbody, where the proof applies.
[`EllipsotopeCentreShift.lean`](../../src/CORALean/Global/EllipsotopeCentreShift.lean)

**`Lemma 26` — the interval and the proof's last steps.** The lemma is stated for
`n ∈ ℕ∖{1}`, which admits n = 0; there L would have to lie in (-1, 0), while the right side of
Eq. 67 is positive, so no such L exists. The paper's setting is n > 1 (Eq. 62), and the
formalization takes n ≥ 2, the condition the proof itself uses at its end. The proof then
proves `L ≤ n` and `L ≥ n - 1` while the claim is the open interval; with `n ≥ 2` both
inequalities it splits into (69, 70) are strict, so the open interval follows, which is
what is formalized. Eq. 70 raised to the p-th power is `n^{-p/(p-1)} ≤ 1 - n^{-p/(p-1)}`,
equivalent to `n ≥ 2^{(p-1)/p} = 2 · 2^{-1/p}`; the printed `2 · 1/2ᵖ ≤ n` has the exponent
on the wrong side of the root, and is not equivalent (at p = 2 it asks `n ≥ 1/2`, the correct
condition is `n ≥ √2`). For `n ≥ 2` both hold, so the conclusion stands.
[`ExistsGadgetRadii.lean`](../../src/CORALean/Global/ExistsGadgetRadii.lean)
