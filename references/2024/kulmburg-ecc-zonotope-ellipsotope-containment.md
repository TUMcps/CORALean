# Search-based and Stochastic Solutions to the Zonotope and Ellipsotope Containment Problems

A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.

**Source:** https://mediatum.ub.tum.de/doc/1750874/1750874.pdf (the authors' version on TUM's repository, carrying the IEEE copyright notice, 8 pages including Appendices A-B, read in full; text extracted with `pypdf`). The IEEE Xplore version was not reachable; the repository copy is the camera-ready one, and its numbering is what CORA cites.  
**Inventory:** confirmed (Definitions 2.1 and 4.1, Proposition 2.2, Theorems 4.2, 4.3 and 4.6, Corollaries 4.7-4.8, Remarks 4.4-4.5 and Algorithms 1-3, numbered by section; the equations below are the numbered displays that make a claim)

Zonotope and ellipsotope containment beyond the co-NP-hardness result of
[Kulmburg and Althoff 2021](../2021/kulmburg-ejc-zonotope-containment.md): an exact
depth-first vertex enumeration with pruning (CORA's `contains_(..., 'exact:venum')`), and
two stochastic methods built on Shenmaier's sampling bound (`'sampling:dual'`,
`'sampling:primal'`). Ellipsotopes are read at any norm on the coefficients, `p`-norms
among them. The search, the sampling bound and the halfspace method's guarantees are
formalized; the probability statements of `Thm. 4.3`, `Thm. 4.6` and the two corollaries
read a confidence level as the probability of containment, which is false, and `Eq. 11`
miscomputes a support function for `p ≠ ∞`.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | The dual norm ‖y‖* = sup_{‖x‖ ≤ 1} yᵀx. | n/a — the textbook dual norm, recalled from Bühler and Salamon; Mathlib's operator norm of a functional | `restated` |
| `Eq. 2` | ‖x‖*_p = ‖x‖_{p*}, p* the Hölder conjugate. | n/a — "a common exercise", recalled from Bühler and Salamon | `restated` |
| `Eq. 3` | The dual set S* = {y \| sup_{x ∈ S} yᵀx ≤ 1}. | n/a — a textbook definition | `restated` |
| `Def. 2.1` | (Ellipsotopes) E_p(G, c) = {c + Gα \| ‖α‖_p ≤ 1}; p = ∞ gives zonotopes. | n/a — restated from Kousik et al. (TAC 2022) | `restated` |
| `Prop. 2.2` | (Ellipsotope norm) For full-rank G, x ↦ min_{Gα = x} ‖α‖_p is a norm whose unit circle coincides with E_p(G). | [`CoeffNormBallEq.lean`](../../src/CORALean/Global/CoeffNormBallEq.lean), [`CoeffNormBallEqCounterexample.lean`](../../src/CORALean/Global/CoeffNormBallEqCounterexample.lean), [`CoeffNorm.lean`](../../src/CORALean/Global/CoeffNorm.lean) — any norm on the coefficients: the norm laws, the unit ball E_p(G) and the unit sphere its boundary; the counterexample to the circle **Counterexample:** `coeffNorm_ball_eq_counterexample` | `fixed` — the unit circle is ∂E_p(G), not E_p(G) (at G = 1 in ℝ¹ it misses 0); the unit ball is E_p(G) |
| `Eq. 6` | Ê ⊆ E iff r(Ê, E) ≤ 1, r = max_{‖α‖_p ≤ 1} ‖Gα + c - d‖_{E_q(H)}. | [`EllipsotopeSubsetIff.lean`](../../src/CORALean/Global/EllipsotopeSubsetIff.lean) — the maximum attained; H onto | `correct` |
| `Eq. 7` | The dual form r = max_{‖Hᵀx‖_{q*} ≤ 1} ‖Gᵀx‖_{p*} + xᵀ(c - d). | n/a — restated from Kulmburg, "The Generalized Matrix Norm Problem", Cor. 3.5 | `restated` |
| `Sec. III` | For a zonotope inbody, by the Bauer maximum principle, the maximum of Eq. 6 is attained at some α ∈ {-1, +1}^m. | [`IsGreatestCoeffNormCorner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IsGreatestCoeffNormCorner.lean) | `correct` |
| `Eq. 9` | (Pruning) er_{k'}(σ') ≤ er_k(σ) + Σ_{i=k+1}^{k'} ‖gᵢ‖ ≤ h_k(σ) for every extension σ' of σ. | [`ContainsDFSIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ContainsDFSIff.lean) — `aux_prune` | `correct` |
| `Alg. 1` | (Depth-First Vertex Enumeration) Sort the generators by norm, search the sign tree depth-first, prune at h_k(σ) ≤ 1, stop at a value above 1; output True iff Ẑ ⊆ E. | [`ContainsDFS.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ContainsDFS.lean), [`ContainsDFSIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ContainsDFSIff.lean) — one `let` per line, the stack a list, the loop on fuel 2^{m+1}; exact for any ellipsotope circumbody with H onto | `correct` |
| `Eq. 10` | (Naive vertex sampling) r_vs = max over sampled sign vectors aᵢ of ‖Gaᵢ + c - d‖_{E_q(H)} satisfies r_vs ≤ r(Ẑ, E). | [`NaiveVertexSampleLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/NaiveVertexSampleLe.lean) — for any sign vectors | `correct` |
| `Eq. 11` | For a non-degenerate zonotope circumbody with facets (Λ, b): r(Ê, Ẑ) = max_α maxᵢ \|λᵢᵀ(Gα + c - d)\|/\|bᵢ\| = maxᵢ ‖G'ᵀλᵢ‖_{p*}/\|bᵢ\|, G' = [G, c - d]. | [`IsGreatestPolyNormEllipsotope.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsGreatestPolyNormEllipsotope.lean), [`IsGreatestPolyNormEllipsotopeCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsGreatestPolyNormEllipsotopeCounterexample.lean) — the maximum as max(0, maxᵢ (‖λᵢ ∘ G‖ + λᵢ(c - d))/bᵢ) at any bᵢ > 0, and the counterexample to the last equality **Counterexample:** `HPolytope.isGreatest_polyNorm_ellipsotope_counterexample` | `fixed` — the support of c + G B_p along λ is ‖Gᵀλ‖_{p*} + λᵀ(c - d), not ‖(Gᵀλ, λᵀ(c - d))‖_{p*}: at p = 2 in ℝ¹ the radius is 2 and the formula gives √2; exact with the sum; see Findings |
| `Eq. 12` | (Naive halfspace sampling) r_hs = max over sampled facets of ‖G'ᵀlᵢ‖_{p*}/\|bᵢ\| satisfies r_hs ≤ r(Ê, Ẑ). | — | — |
| `Def. 4.1` | (ϑ-uniform) \|P(v ∈ S) - vol(S)/vol(K)\| ≤ ϑ for every measurable S ⊆ K. | [`ThetaUniform.lean`](../../src/CORALean/Global/ThetaUniform.lean) | `correct` |
| `Thm. 4.2` | For compact K, a norm with ball B and N independent ϑ-uniform samples vᵢ ∈ B with zᵢ = argmax_{z ∈ B*} zᵀvᵢ: r_S = maxᵢ max_{x ∈ K} zᵢᵀx ≤ max_K ‖x‖ (Eq. 16), and (1 - ε) max_K ‖x‖ ≤ r_S with probability at least P_S(ε) = 1 - (1 - (ε/(2+ε))ⁿ + ϑ)^N (Eq. 17-18). | [`ShenmaierBound.lean`](../../src/CORALean/Global/ShenmaierBound.lean) — any norm function on a finite-dimensional space, continuous and above a multiple of the ambient norm, a Haar volume; zᵢ ∈ B* with zᵢvᵢ = ‖vᵢ‖, which the argmax gives; ϑ ≥ 0 | `correct` |
| `Eq. 19` | (Support function) max_{x ∈ E_p(G, c)} zᵀx = ‖Gᵀz‖_{p*} + zᵀc. | [`EllipsotopeSupport.lean`](../../src/CORALean/Global/EllipsotopeSupport.lean) — ‖Gᵀz‖_{p*} as the operator norm of z ∘ G (Eq. 1) | `correct` |
| `Thm. 4.3` | For Alg. 2 with non-degenerate E: Ê ⊄ E if r_Shs > 1, and P_Shs is a lower bound on the probability that Ê ⊆ E if r_Shs ≤ 1. | [`ShenmaierHalfspaceNotSubset.lean`](../../src/CORALean/Global/ShenmaierHalfspaceNotSubset.lean), [`ShenmaierHalfspaceProb.lean`](../../src/CORALean/Global/ShenmaierHalfspaceProb.lean), [`ShenmaierHalfspaceCounterexample.lean`](../../src/CORALean/Global/ShenmaierHalfspaceCounterexample.lean) — the first half as printed; the second at a fixed ε, P((1 - ε) r(Ê, E) ≤ r_Shs) ≥ P_S(ε); the counterexample to the printed second half **Counterexample:** `shenmaierHalfspace_counterexample` **Counterexample:** `shenmaierHalfspace_counterexample` | `fixed` — Ê ⊆ E is not random: with Ê ⊄ E, one sample of [-1, 1]² returns P_Shs ≈ 0.086 > 0 = P(Ê ⊆ E); the proof picks ε = 1 - r_Shs after sampling; true at a fixed ε; see Findings |
| `Remark 4.4` | Line 2 of Alg. 2 is a convex problem with a linear objective, solvable in polynomial time by interior-point methods. | n/a — a remark on solvers | `not-a-claim` |
| `Remark 4.5` | Uniform samples of E_q(H) can be drawn by the ball walk of Lovász and Simonovits (preconditions in App. B). | n/a — a remark on the sampler | `not-a-claim` |
| `Alg. 2` | (Shenmaier Halfspace Sampling) zᵢ = argmax_{‖Hᵀz‖* ≤ 1} zᵀvᵢ, r_{Shs,i} = ‖Gᵀzᵢ‖_{p*} + zᵢᵀ(c - d), r_Shs = maxᵢ; False if r_Shs > 1, else P_S(1 - r_Shs). | [`ShenmaierHalfspace.lean`](../../src/CORALean/Global/ShenmaierHalfspace.lean), [`ShenmaierHalfspaceNotSubset.lean`](../../src/CORALean/Global/ShenmaierHalfspaceNotSubset.lean) — samples and maximizers supplied (lines 1-2) | `correct` |
| `Thm. 4.6` | For Alg. 3: Ê ⊄ E if r_Svs > 1, and P_Svs is a lower bound on the probability that Ê ⊆ E if r_Svs ≤ 1. | — | — |
| `Alg. 3` | (Shenmaier Vertex Sampling) vᵢ uniform on B_{p*}, zᵢ = argmax_{z ∈ B_p} zᵀvᵢ (Eq. 21), r_{Svs,i} = ‖Gzᵢ + c - d‖_{E_q(H)}, r_Svs = maxᵢ; False if r_Svs > 1, else P_S(1 - r_Svs) at ϑ = 0. | [`ShenmaierVertex.lean`](../../src/CORALean/Global/ShenmaierVertex.lean), [`ShenmaierVertexNotSubset.lean`](../../src/CORALean/Global/ShenmaierVertexNotSubset.lean) — the zᵢ supplied; its False is certain | `correct` |
| `Eq. 21` | argmax_{z ∈ B_p} zᵀx = sign(x) ∘ \|x\|^{p*-1}/‖x‖_{p*}^{p*-1}. | n/a — recalled from Bhattiprolu et al., Sec. 2.2 | `restated` |
| `Cor. 4.7` | For naive vertex sampling: Ẑ ⊄ E if r_vs > 1, and Ẑ ⊆ E with probability at least P_S(1 - r_vs) if r_vs ≤ 1. | — | — |
| `Cor. 4.8` | For naive halfspace sampling: Ê ⊄ Ẑ if r_hs > 1, and Ê ⊆ Ẑ with probability at least P_S(1 - r_hs) if r_hs ≤ 1. | — | — |
| `Sec. V` | Runtime of Alg. 1 against plain vertex enumeration, accuracy of the sampling methods, a quadrotor reaching an ellipsoidal target (Figs. 1-3, Table I). | n/a — experiments | `not-a-claim` |
| `App. B` | Rounding for the ball walk: B₂ ⊆ B_q ⊆ n^{1/2-1/q}B₂ (q ≥ 2, reversed for q ≤ 2), and via the SVD of H, B₂ ⊆ E_q(D⁻¹UᵀH) ⊆ n^{1/2-1/q}B₂; polynomial time. | — | — |

## Findings

**`Thm. 4.3`, and the probability halves of `Thm. 4.6`, `Cor. 4.7`, `Cor. 4.8`.** Each says
that when the sampled value r ≤ 1, P_S(1 - r) "is a lower bound on the probability that
Ê ⊆ E". Containment of two given sets is not random: its probability is 0 or 1. The proof
takes `Thm. 4.2`'s bound, which holds for a fixed ε, at ε = 1 - r chosen after the samples
are seen. Concretely, in ℝ² with the supremum norm, E = [-1, 1]² and
Ê = (21/20, 0) + [-1/10, 1/10]² ⊄ E; the single sample v = (0, 1/2) with z = e₂ᵀ gives
r_Shs ≤ 1/10 and, at ϑ = 1/100, P_Shs ≥ (9/29)² - 1/100 > 0, under any measure on the
samples. What holds is the fixed-ε statement: P((1 - ε) r(Ê, E) ≤ r_Shs) ≥ P_S(ε), so if
Ê ⊄ E the algorithm reports a value above 1 - ε with probability at least P_S(ε) —
formalized for `Alg. 2`. For `Alg. 3` (and so `Cor. 4.7`) even the fixed-ε statement is not
established by the printed argument when c ≠ d: `Thm. 4.2` is applied to K = Gᵀ(E_q(H))*,
whose largest p*-norm is r(Ê, E) only through Eq. 7 at c = d; those rows stay open, with
the certain half of `Thm. 4.6` formalized.
[`ShenmaierHalfspaceCounterexample.lean`](../../src/CORALean/Global/ShenmaierHalfspaceCounterexample.lean),
[`ShenmaierHalfspaceProb.lean`](../../src/CORALean/Global/ShenmaierHalfspaceProb.lean),
[`ShenmaierVertexNotSubset.lean`](../../src/CORALean/Global/ShenmaierVertexNotSubset.lean)

**`Eq. 11` — the support function of the shifted inbody.** The last step writes
max_{‖α‖_p ≤ 1} \|λᵀ(Gα + c - d)\| as ‖G'ᵀλ‖_{p*} with G' = [G, c - d]. The maximum is
‖Gᵀλ‖_{p*} + \|λᵀ(c - d)\|; ‖(a, s)‖_{p*} equals ‖a‖_{p*} + \|s\| only at p* = 1 (a
zonotope inbody) or when one of them vanishes. In ℝ¹ with Ê = E₂(1, 1) = [0, 2],
Ẑ = [-1, 1]: r = 2, the formula gives √2. Since ‖(a, s)‖_{p*} ≤ ‖a‖_{p*} + \|s\|, the
printed value under-estimates, so `Cor. 4.8`'s "Ê ⊄ Ẑ if r_hs > 1" survives; its accuracy
statement does not. CORA's `priv_zonotopeContainment_ellipsoidSamplingDual.m` computes
exactly this formula (`sqrt(sum((G_prime' * lambda).^2))`).
[`IsGreatestPolyNormEllipsotopeCounterexample.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsGreatestPolyNormEllipsotopeCounterexample.lean)

**`Prop. 2.2` — circle for ball.** "Its unit circle coincides with E_p(G)": the unit ball
does; the circle is the boundary. [`CoeffNormBallEqCounterexample.lean`](../../src/CORALean/Global/CoeffNormBallEqCounterexample.lean)
