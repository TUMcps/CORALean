# Search-based and Stochastic Solutions to the Zonotope and Ellipsotope Containment Problems

```bibtex
@inproceedings{kulmburg2024search,
  author = {Kulmburg, A. and Brkan, I. and Althoff, M.},
  title = {Search-based and Stochastic Solutions to the Zonotope and Ellipsotope Containment Problems},
  booktitle = {2024 European Control Conference (ECC)},
  year = {2024}
}
```

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
| `Prop. 2.2` | (Ellipsotope norm) For full-rank G, x ↦ min_{Gα = x} ‖α‖_p is a norm whose unit circle coincides with E_p(G). | [`CoeffNormBallEq.lean`](../../src/CORALean/Global/CoeffNormBallEq.lean), [`CoeffNormBallEq.lean`](../../src/CORALean/Global/Counterexamples/CoeffNormBallEq.lean), [`CoeffNorm.lean`](../../src/CORALean/Global/CoeffNorm.lean) — any norm on the coefficients: the norm laws, the unit ball E_p(G) and the unit sphere its boundary; the counterexample to the circle **Counterexample:** `coeffNorm_ball_eq_counterexample` | `fixed` — the unit circle is ∂E_p(G), not E_p(G) (at G = 1 in ℝ¹ it misses 0); the unit ball is E_p(G) |
| `Eq. 6` | Ê ⊆ E iff r(Ê, E) ≤ 1, r = max_{‖α‖_p ≤ 1} ‖Gα + c - d‖_{E_q(H)}. | [`EllipsotopeSubsetIff.lean`](../../src/CORALean/Global/EllipsotopeSubsetIff.lean) — the maximum attained; H onto | `correct` |
| `Eq. 7` | The dual form r = max_{‖Hᵀx‖_{q*} ≤ 1} ‖Gᵀx‖_{p*} + xᵀ(c - d). | n/a — restated from Kulmburg, "The Generalized Matrix Norm Problem", Cor. 3.5 | `restated` |
| `Sec. III` | For a zonotope inbody, by the Bauer maximum principle, the maximum of Eq. 6 is attained at some α ∈ {-1, +1}^m. | [`IsGreatestCoeffNormCorner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IsGreatestCoeffNormCorner.lean) | `correct` |
| `Eq. 9` | (Pruning) er_{k'}(σ') ≤ er_k(σ) + Σ_{i=k+1}^{k'} ‖gᵢ‖ ≤ h_k(σ) for every extension σ' of σ. | [`ContainsDFSIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ContainsDFSIff.lean) — `aux_prune` | `correct` |
| `Alg. 1` | (Depth-First Vertex Enumeration) Sort the generators by norm, search the sign tree depth-first, prune at h_k(σ) ≤ 1, stop at a value above 1; output True iff Ẑ ⊆ E. | [`ContainsDFS.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ContainsDFS.lean), [`ContainsDFSIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ContainsDFSIff.lean) — one `let` per line, the stack a list, the loop on fuel 2^{m+1}; exact for any ellipsotope circumbody with H onto | `correct` |
| `Eq. 10` | (Naive vertex sampling) r_vs = max over sampled sign vectors aᵢ of ‖Gaᵢ + c - d‖_{E_q(H)} satisfies r_vs ≤ r(Ẑ, E). | [`NaiveVertexSampleLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/NaiveVertexSampleLe.lean) — for any sign vectors | `correct` |
| `Eq. 11` | For a non-degenerate zonotope circumbody with facets (Λ, b): r(Ê, Ẑ) = max_α maxᵢ \|λᵢᵀ(Gα + c - d)\|/\|bᵢ\| = maxᵢ ‖G'ᵀλᵢ‖_{p*}/\|bᵢ\|, G' = [G, c - d]. | [`IsGreatestPolyNormEllipsotope.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsGreatestPolyNormEllipsotope.lean), [`IsGreatestPolyNormEllipsotope.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IsGreatestPolyNormEllipsotope.lean) — the maximum as max(0, maxᵢ (‖λᵢ ∘ G‖ + λᵢ(c - d))/bᵢ) at any bᵢ > 0, and the counterexample to the last equality **Counterexample:** `HPolytope.isGreatest_polyNorm_ellipsotope_counterexample` | `fixed` — the support of c + G B_p along λ is ‖Gᵀλ‖_{p*} + λᵀ(c - d), not ‖(Gᵀλ, λᵀ(c - d))‖_{p*}: at p = 2 in ℝ¹ the radius is 2 and the formula gives √2; exact with the sum; see Findings |
| `Eq. 12` | (Naive halfspace sampling) r_hs = max over sampled facets of ‖G'ᵀlᵢ‖_{p*}/\|bᵢ\| satisfies r_hs ≤ r(Ê, Ẑ). | [`NaiveHalfspaceValue.lean`](../../src/CORALean/ContSet/HPolytope/Real/Definitions/NaiveHalfspaceValue.lean), [`NaiveHalfspaceValueLe.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/NaiveHalfspaceValueLe.lean) — for any sampled facets of a zonotope circumbody `{Λx ≤ b}` (`bᵢ > 0`, the rows closed under `λ ↦ -λ`), `maxᵢ ‖G'ᵀλ_{jᵢ}‖_{p*}/\|b_{jᵢ}\| ≤ r(Ê, Ẑ)`, the radius the maximum of `Eq. 11`'s first form; the `p*`-norm of `G'ᵀλ` is the operator norm of the row on `E × ℝ` with the `ℓ_p` combination of the norms, `ℓ_p^{m+1}` for `E = ℓ_p^m` | `correct` |
| `Def. 4.1` | (ϑ-uniform) \|P(v ∈ S) - vol(S)/vol(K)\| ≤ ϑ for every measurable S ⊆ K. | [`ThetaUniform.lean`](../../src/CORALean/Global/ThetaUniform.lean) | `correct` |
| `Thm. 4.2` | For compact K, a norm with ball B and N independent ϑ-uniform samples vᵢ ∈ B with zᵢ = argmax_{z ∈ B*} zᵀvᵢ: r_S = maxᵢ max_{x ∈ K} zᵢᵀx ≤ max_K ‖x‖ (Eq. 16), and (1 - ε) max_K ‖x‖ ≤ r_S with probability at least P_S(ε) = 1 - (1 - (ε/(2+ε))ⁿ + ϑ)^N (Eq. 17-18). | [`ShenmaierBound.lean`](../../src/CORALean/Global/ShenmaierBound.lean) — any norm function on a finite-dimensional space, continuous and above a multiple of the ambient norm, a Haar volume; zᵢ ∈ B* with zᵢvᵢ = ‖vᵢ‖, which the argmax gives; ϑ ≥ 0 | `correct` |
| `Eq. 19` | (Support function) max_{x ∈ E_p(G, c)} zᵀx = ‖Gᵀz‖_{p*} + zᵀc. | [`EllipsotopeSupport.lean`](../../src/CORALean/Global/EllipsotopeSupport.lean) — ‖Gᵀz‖_{p*} as the operator norm of z ∘ G (Eq. 1) | `correct` |
| `Thm. 4.3` | For Alg. 2 with non-degenerate E: Ê ⊄ E if r_Shs > 1, and P_Shs is a lower bound on the probability that Ê ⊆ E if r_Shs ≤ 1. | [`ShenmaierHalfspaceNotSubset.lean`](../../src/CORALean/Global/ShenmaierHalfspaceNotSubset.lean), [`ShenmaierHalfspaceProb.lean`](../../src/CORALean/Global/ShenmaierHalfspaceProb.lean), [`ShenmaierHalfspace.lean`](../../src/CORALean/Global/Counterexamples/ShenmaierHalfspace.lean) — the first half as printed; the second at a fixed ε, P((1 - ε) r(Ê, E) ≤ r_Shs) ≥ P_S(ε); the counterexample to the printed second half **Counterexample:** `shenmaierHalfspace_counterexample` **Counterexample:** `shenmaierHalfspace_counterexample` | `fixed` — Ê ⊆ E is not random: with Ê ⊄ E, one sample of [-1, 1]² returns P_Shs ≈ 0.086 > 0 = P(Ê ⊆ E); the proof picks ε = 1 - r_Shs after sampling; true at a fixed ε; see Findings |
| `Remark 4.4` | Line 2 of Alg. 2 is a convex problem with a linear objective, solvable in polynomial time by interior-point methods. | n/a — a remark on solvers | `not-a-claim` |
| `Remark 4.5` | Uniform samples of E_q(H) can be drawn by the ball walk of Lovász and Simonovits (preconditions in App. B). | n/a — a remark on the sampler | `not-a-claim` |
| `Alg. 2` | (Shenmaier Halfspace Sampling) zᵢ = argmax_{‖Hᵀz‖* ≤ 1} zᵀvᵢ, r_{Shs,i} = ‖Gᵀzᵢ‖_{p*} + zᵢᵀ(c - d), r_Shs = maxᵢ; False if r_Shs > 1, else P_S(1 - r_Shs). | [`ShenmaierHalfspace.lean`](../../src/CORALean/Global/ShenmaierHalfspace.lean), [`ShenmaierHalfspaceNotSubset.lean`](../../src/CORALean/Global/ShenmaierHalfspaceNotSubset.lean) — samples and maximizers supplied (lines 1-2) | `correct` |
| `Thm. 4.6` | For Alg. 3: Ê ⊄ E if r_Svs > 1, and P_Svs is a lower bound on the probability that Ê ⊆ E if r_Svs ≤ 1. | [`ShenmaierVertexNotSubset.lean`](../../src/CORALean/Global/ShenmaierVertexNotSubset.lean), [`ShenmaierVertex.lean`](../../src/CORALean/Global/Counterexamples/ShenmaierVertex.lean), [`ShenmaierVertexProb.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ShenmaierVertexProb.lean), [`L1BallOrthantVolume.lean`](../../src/CORALean/Global/L1BallOrthantVolume.lean) — the first half as printed; the counterexample to the printed second half **Counterexample:** `shenmaierVertex_counterexample`; at `p = ∞` (a zonotope `Ê`) and fixed `ε`, `P((1 - ε) r(Ê, E) ≤ r_Svs) ≥ P_S(ε)` for `ϑ`-uniform samples of `B₁`, with the dimension `m` of the coefficients in `P_S` | `fixed` — `P_Svs` is not a probability that `Ê ⊆ E`, which is not random: with `Ê ⊄ E`, one sample of `B₁` returns `P_Svs > 0 = P(Ê ⊆ E)`; true at a fixed `ε`, proved at `p = ∞` only; see Findings |
| `Alg. 3` | (Shenmaier Vertex Sampling) vᵢ uniform on B_{p*}, zᵢ = argmax_{z ∈ B_p} zᵀvᵢ (Eq. 21), r_{Svs,i} = ‖Gzᵢ + c - d‖_{E_q(H)}, r_Svs = maxᵢ; False if r_Svs > 1, else P_S(1 - r_Svs) at ϑ = 0. | [`ShenmaierVertex.lean`](../../src/CORALean/Global/ShenmaierVertex.lean), [`ShenmaierVertexNotSubset.lean`](../../src/CORALean/Global/ShenmaierVertexNotSubset.lean) — the zᵢ supplied; its False is certain | `correct` |
| `Eq. 21` | argmax_{z ∈ B_p} zᵀx = sign(x) ∘ \|x\|^{p*-1}/‖x‖_{p*}^{p*-1}. | n/a — recalled from Bhattiprolu et al., Sec. 2.2 | `restated` |
| `Cor. 4.7` | For naive vertex sampling: Ẑ ⊄ E if r_vs > 1, and Ẑ ⊆ E with probability at least P_S(1 - r_vs) if r_vs ≤ 1. | [`NaiveVertexSampleNotSubset.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/NaiveVertexSampleNotSubset.lean), [`NaiveVertexSampleProb.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/NaiveVertexSampleProb.lean), [`NaiveVertexSamplePrinted.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/NaiveVertexSamplePrinted.lean) — the first half as printed; at a fixed `ε` and `N` independent uniform sign vectors, `P((1 - ε) r(Ẑ, Ê) ≤ r_vs) ≥ P_S(ε)` at `ϑ = 0` and the number `m` of generators as `n`; the counterexample to the printed second half **Counterexample:** `Zonotope.naive_vertex_sample_printed_counterexample` | `fixed` — `Ẑ ⊆ Ê` is not random: with `Ẑ ⊄ Ê`, one sampled corner of norm `19/20` gives `P_S(1/20) > 0 = P(Ẑ ⊆ Ê)`; true at a fixed `ε`; see Findings |
| `Cor. 4.8` | For naive halfspace sampling: Ê ⊄ Ẑ if r_hs > 1, and Ê ⊆ Ẑ with probability at least P_S(1 - r_hs) if r_hs ≤ 1. | [`NaiveHalfspaceNotSubset.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/NaiveHalfspaceNotSubset.lean), [`NaiveHalfspacePrinted.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/NaiveHalfspacePrinted.lean), [`NaiveHalfspaceAccuracy.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/NaiveHalfspaceAccuracy.lean) — the first half as printed (`Ê ⊄ Ẑ` if `r_hs > 1`, from `Eq. 12`); the counterexample to the printed second half **Counterexample:** `HPolytope.naiveHalfspace_printed_counterexample`, and to the fixed-`ε` accuracy of `r_hs` **Counterexample:** `HPolytope.naiveHalfspace_accuracy_counterexample` | `false` — `Ê ⊆ Ẑ` is not random (one sampled facet gives `P_S(9/10) > 0` for `Ê ⊄ Ẑ`), and the printed `r_hs` falls short of the radius by `Eq. 11`'s error, so not even `r_hs ≥ (1 - ε) r` holds with a probability `P_S(ε) > 0` (`ℝ¹`, `p = 2`: `r = 2`, `r_hs ≤ √2`); no corrected version of this statement is proved; see Findings |
| `Sec. V` | Runtime of Alg. 1 against plain vertex enumeration, accuracy of the sampling methods, a quadrotor reaching an ellipsoidal target (Figs. 1-3, Table I). | n/a — experiments | `not-a-claim` |
| `App. B` | Rounding for the ball walk: B₂ ⊆ B_q ⊆ n^{1/2-1/q}B₂ (q ≥ 2, reversed for q ≤ 2), and via the SVD of H, B₂ ⊆ E_q(D⁻¹UᵀH) ⊆ n^{1/2-1/q}B₂. | [`LpNormLeLpNorm.lean`](../../src/CORALean/Global/LpNormLeLpNorm.lean), [`LpNormLeCardRpowMul.lean`](../../src/CORALean/Global/LpNormLeCardRpowMul.lean), [`NormTwoSqEqDotProduct.lean`](../../src/CORALean/Global/NormTwoSqEqDotProduct.lean), [`NormTwoTransposeMulVecEq.lean`](../../src/CORALean/Global/NormTwoTransposeMulVecEq.lean), [`NormTwoMulVecLe.lean`](../../src/CORALean/Global/NormTwoMulVecLe.lean), [`EllipsotopeRoundingOfTwoLe.lean`](../../src/CORALean/Global/EllipsotopeRoundingOfTwoLe.lean), [`EllipsotopeRoundingOfLeTwo.lean`](../../src/CORALean/Global/EllipsotopeRoundingOfLeTwo.lean), [`EllipsotopeRounding.lean`](../../src/CORALean/Global/Counterexamples/EllipsotopeRounding.lean) — `‖x‖_q ≤ ‖x‖_p ≤ m^{1/p-1/q}‖x‖_q` for `1 ≤ p ≤ q ≤ ∞`; for `M Mᵀ = I` (`D⁻¹UᵀH = [I 0]Vᵀ`), `B₂ ⊆ E_q(M) ⊆ m^{1/2-1/q}B₂` for `q ≥ 2` and `B₂ ⊆ m^{1/q-1/2}E_q(M) ⊆ m^{1/q-1/2}B₂` for `1 ≤ q ≤ 2`, `m` the number of generators; the counterexample to the printed `n` **Counterexample:** `ellipsotope_rounding_counterexample` | `fixed` — the exponent is the dimension `m` of the coefficients `B_q` lives in, not the printed `n` of the image: `n = 1`, `m = 2`, `q = ∞`, `M = (√2/2, √2/2)` has `√2 ∈ E_∞(M)` outside `1^{1/2}B₂`; see Findings |
| `App. B (complexity)` | The whole procedure runs in polynomial time in the dimension `n` and the number of generators `m`: the singular value decomposition is polynomial and the ball walk is polynomial by [12, Thm. 3.7]. | n/a — a running time, which a Lean definition does not state | `not-a-claim` |

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
[`ShenmaierHalfspace.lean`](../../src/CORALean/Global/Counterexamples/ShenmaierHalfspace.lean),
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
[`IsGreatestPolyNormEllipsotope.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IsGreatestPolyNormEllipsotope.lean)

**`Prop. 2.2` — circle for ball.** "Its unit circle coincides with E_p(G)": the unit ball
does; the circle is the boundary. [`CoeffNormBallEq.lean`](../../src/CORALean/Global/Counterexamples/CoeffNormBallEq.lean)

**`Thm. 4.6`, `Cor. 4.7`, `Cor. 4.8` — what is true.** The probability halves have the failure
described for `Thm. 4.3`: `Ẑ ⊆ Ê` is not random, and each of the three has an instance where `r ≤ 1`
is sampled and `P_S(1 - r) > 0` is returned for sets that are not nested (for `Alg. 3` and
`Cor. 4.7` in `ℝ²` with the supremum norm and `Ê = (21/20, 0) + [-1/10, 1/10]²` against `[-1, 1]²`,
one sample of norm `19/20`; for `Cor. 4.8` the facet `x₂ ≤ 1`). What holds is the fixed-`ε`
statement. For naive vertex sampling it is `P((1 - ε) r ≤ r_vs) ≥ P_S(ε)` with `N` independent
uniform sign vectors, because the maximum is attained at one of the `2ᵐ` corners, which a sample
is with probability `2⁻ᵐ ≥ (ε/(2+ε))ᵐ`; with the ambient dimension `n` as the exponent of `P_S`
it fails when the number of generators `m` is larger than `n`, so `P_S` is read at `m`, the
dimension of the cube sampled. `Alg. 3` at `p = ∞` is that sampling for `ϑ`-uniform `v` on `B₁`:
the maximizer of `zᵀv` is `sign(v)` off the coordinate hyperplanes, and the open orthant of the
optimal corner carries `2⁻ᵐ` of the ball, so the same bound holds with `ϑ`. For other `p` the
fixed-`ε` statement of `Alg. 3` is not established by the printed argument (see above) and stays
open. For `Cor. 4.8` the printed `r_hs` under-estimates the radius (`Eq. 11`), so the fixed-`ε`
statement fails as printed too: in `ℝ¹` with `p = 2`, `Ê = [0, 2]` and `Ẑ = [-1, 1]` the radius is
`2` and every sample of the facets gives `r_hs ≤ √2 < (1 - 1/10) 2`, while `P_S(1/10) > 0`.
[`ShenmaierVertex.lean`](../../src/CORALean/Global/Counterexamples/ShenmaierVertex.lean),
[`ShenmaierVertexProb.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ShenmaierVertexProb.lean),
[`NaiveVertexSampleProb.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/NaiveVertexSampleProb.lean),
[`NaiveVertexSamplePrinted.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/NaiveVertexSamplePrinted.lean),
[`NaiveHalfspacePrinted.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/NaiveHalfspacePrinted.lean),
[`NaiveHalfspaceAccuracy.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/NaiveHalfspaceAccuracy.lean)

**`App. B` — the dimension of the rounding.** `B₂ ⊆ B_q ⊆ n^{1/2-1/q}B₂` is the comparison of
the `ℓ_q` and `ℓ₂` norms of `ℝᵏ` with `k` the dimension of the ball, `‖x‖_q ≤ ‖x‖₂ ≤ k^{1/2-1/q}‖x‖_q`.
The ellipsotope's balls are those of its coefficients, in `ℝᵐ` for `m` generators, so the factor of
`E_q(H) = H B_q` and of `E_q(D⁻¹UᵀH)` is `m^{1/2-1/q}`, not `n^{1/2-1/q}` with `n` the dimension of
the image: with one row and two generators, `E_∞(M) = [-√2, √2]` is not inside the unit ball
(`n^{1/2} = 1`). The rows of `D⁻¹UᵀH = [I 0]Vᵀ` are orthonormal, which is all the inclusions need.
For `q ≤ 2` the factor is `m^{1/q-1/2}`, as printed with `n` replaced by `m`. The singular value
decomposition itself is a hypothesis of the factorization, not constructed.
[`EllipsotopeRoundingOfTwoLe.lean`](../../src/CORALean/Global/EllipsotopeRoundingOfTwoLe.lean),
[`EllipsotopeRounding.lean`](../../src/CORALean/Global/Counterexamples/EllipsotopeRounding.lean)
