# Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov Subspace

M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.

**Source:** https://arxiv.org/pdf/1712.00369 (arXiv:1712.00369v2, 5 Aug 2020, the author's version, 16 pages including Appendices A-B, read in full; text extracted with `pypdf`). The typeset IEEE article (doi:10.1109/TAC.2019.2906432) was not reachable; numbering is the arXiv version's, which has the TAC article's section-based labels. CORA's Krylov files (`linearSys/private/priv_reach_krylov.m`, `priv_initReach_Krylov.m`, `priv_inputSolution_Krylov.m`, `priv_exponential_Krylov*.m`) cite the paper without result numbers.  
**Inventory:** confirmed (Definition II.1, Lemmas III.1-III.3 and IV.1, Theorems III.1-III.2 and IV.1-IV.2, Corollaries IV.1-IV.2, Proposition B.1, Algorithms 1-2, equations (1)-(35); the rows below are the results and the numbered displays that make a claim)

Reachable sets of linear systems with several thousand states and arbitrarily varying
bounded inputs, by computing `e^{At}v` in a Krylov subspace (Arnoldi, `Alg. 1`) and carrying
the approximation error as a box. The approximation error itself is Wang and Ye's
a-posteriori bound (3), cited; here it is a hypothesis, as the brief for Krylov error bounds
asks. Formalized: the Arnoldi relation for `Alg. 1` and the exactness it gives below the Krylov
order, the error box (`Lemma III.1`), the
zonotope enclosures built from per-vector boxes (`Thm. III.1`, `Thm. IV.1`), the interval
vector bound (`Lemma III.2`), the correction matrix in the subspace (`Lemma III.3`), the
time-interval enclosure (`Thm. III.2`, corrected), the augmented-system identity behind
`Lemma IV.1`, the input solution over part of a step (`Cor. IV.1`, corrected) and the error
bound's linear-in-time form (`Prop. B.1`). `Thm. III.2` and `Cor. IV.1` are false as printed
(Findings). The varying-input results (`Thm. IV.2`, `Cor. IV.2`) and `Alg. 2` built on them are
open; formalized of them are the Krylov Taylor terms for varying inputs below the Krylov order
(with the thesis' remainder in place of the Krylov one) and `Alg. 2`'s input propagation, whose
line 8 is one step off.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Alg. 1` | (Arnoldi iteration) v⁽¹⁾ = v/‖v‖; for k = 1…ξ: w = Cv⁽ᵏ⁾, h_{j,k} = w*v⁽ʲ⁾ and w := w - h_{j,k}v⁽ʲ⁾ for j = 1…k, h_{k+1,k} = ‖w‖, happy breakdown if h_{k+1,k} ≤ tol‖C‖, v⁽ᵏ⁺¹⁾ = w/h_{k+1,k}; the result is an orthogonal basis V of K_ξ and the upper Hessenberg H. | [`Arnoldi.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Operations/Arnoldi.lean), [`GramSchmidtStep.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Operations/GramSchmidtStep.lean), [`ArnoldiRelation.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ArnoldiRelation.lean), [`ArnoldiBasis.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Operations/ArnoldiBasis.lean), [`ArnoldiHessenberg.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Operations/ArnoldiHessenberg.lean), [`PowMulVecOfHessenberg.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PowMulVecOfHessenberg.lean), [`ArnoldiBasisMulVecPow.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ArnoldiBasisMulVecPow.lean) — the listing over ℝ; the Arnoldi relation C v⁽ᵏ⁾ = Σ_{i≤k} h_{i,k}v⁽ⁱ⁾ + h_{k+1,k}v⁽ᵏ⁺¹⁾ for every column, a happy breakdown included (the residual is then 0); and with it V H^j e₁ = C^j v/‖v‖ for j < ξ, the approximation (1) exact below the Krylov order; orthogonality of V is not shown | `underspecified` — the happy breakdown (line 10) names no action; read as stopping at ξ = k, so that only columns with h_{k+1,k} ≠ 0 are formed |
| `Eq. 1` | e^C v ≈ ‖v‖Ve^H e₁, and (2) e^{Ct}v ≈ ‖v‖Ve^{Ht}e₁. | n/a — approximations, quantified by (3) | `not-a-claim` |
| `Sec. II-A` | The a-priori bound ‖e^{Ct}v - ‖v‖Ve^{Ht}e₁‖ ≤ 2‖v‖‖Ct‖^ξ e^{‖Ct‖}/ξ!. | n/a — restated from Saad 1992 [55, eq. 29] | `restated` |
| `Eq. 3` | (A-posteriori bound) ∀t ∈ [0, t_f]: ‖e^{Ct}v - ‖v‖Ve^{Ht}e₁‖ ≤ ‖v‖ε_norm t, ε_norm as in Appendix B. | n/a — restated from Wang and Ye [58, Eq. 4.1] through `Prop. B.1`; the hypothesis of the results below | `restated` |
| `Def. II.1` | (Zonotope) Z = {c + Σβᵢg⁽ⁱ⁾ \| βᵢ ∈ [-1, 1]} = (c, g⁽¹⁾, …, g⁽ᵖ⁾), order p/n. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 4` | Z₁ ⊕ Z₂ and MZ₁ by concatenating and mapping generators. | n/a — restated from [60] | `restated` |
| `Eq. 5` | conv(Z₁, Z₂) ⊆ ½(c + d, g + h, c - d, g - h) for zonotopes of equal order. | n/a — restated from Girard 2005 [22] | `restated` |
| `Sec. II-B` | An interval matrix M ⊕ [-S, S] times a zonotope is enclosed by (Mc, Mg⁽ⁱ⁾, h⁽ʲ⁾), h⁽ʲ⁾ = Sⱼ(\|c\| + Σ\|g⁽ᵏ⁾\|)eⱼ. | n/a — restated from Althoff's thesis [61, Thm. 3.3] | `restated` |
| `Eq. 6` | box(Z) = (c, ĥ⁽¹⁾, …, ĥ⁽ⁿ⁾), ĥ⁽ⁱ⁾ⱼ = (Σ\|g⁽ᵏ⁾\|)ⱼ for i = j. | n/a — restated from Althoff's thesis [61, Prop. 2.2] | `restated` |
| `Eq. 9` | (Exact reachable set) R^e([0, t_f]) = {χ(t; x₀, u(·)) \| x₀ ∈ R(0), t ∈ [0, t_f], u(τ) ∈ U}. | n/a — restated; tracked as `Def. 3.1` on [Althoff's thesis](../2010/althoff-thesis.md) | `restated` |
| `Lemma III.1` | (Single state homogeneous solution) With V, H from Alg. 1 for C = A, v = x₀: x_h(t) = e^{At}x₀ ∈ ‖x₀‖Ve^{Ht}e₁ ⊕ [-1, 1]ⁿ‖x₀‖ε_norm t (10). | [`MemBoxOfNormLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/MemBoxOfNormLe.lean) — from (3) as hypothesis, for any vector and approximation | `correct` |
| `Thm. III.1` | (Homogeneous solution for a point in time) For X₀ = (c, g⁽¹⁾, …, g⁽ᵖ⁾): e^{At}X₀ ⊆ (ĉ, ĝ⁽¹⁾, …, ĝ⁽ᵖ⁾) ⊕ [-1, 1]ⁿ(‖c‖ + Σ‖g⁽ⁱ⁾‖)ε_norm t, ĉ, ĝ⁽ⁱ⁾ the Krylov approximations of e^{At}c, e^{At}g⁽ⁱ⁾. | [`ImageSubsetOfApprox.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ImageSubsetOfApprox.lean) — any linear map, from Lemma III.1's box at c and at each g⁽ⁱ⁾ | `underspecified` — ε_norm is computed per vector (Appendix B: h_{ξ+1,ξ} and ω come from that vector's Arnoldi run), and one ε_norm for c and every g⁽ⁱ⁾ holds only as their maximum; the formalization takes one bound per vector, as Thm. IV.1 does |
| `Eq. 12` | [-1, 1]ⁿ ε̂_norm t = ⊕ᵢ [-1, 1]eᵢ ε̂_norm t, the box as a zonotope with n generators. | n/a — the box as a zonotope, restated from [61] | `restated` |
| `Lemma III.2` | (Interval vector multiplication) For [b̲, b̄] = b_c ⊕ [-b_Δ, b_Δ]: e^{At}[b̲, b̄] ⊆ ‖b_c‖V(b_c)e^{H(b_c)t}e₁ ⊕ [-μ, μ], μ = ‖b_Δ‖V̄(b_Δ)e^{H̄(b_Δ)t}e₁ + 1ₙ(‖b_Δ‖ε̄_norm t + ‖b_c‖ε_norm t), V̄, H̄ from C = \|A\|. | [`ExpMulIntervalSubset.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ExpMulIntervalSubset.lean) — coordinate by coordinate, from (3) at (A, b_c) and (\|A\|, b_Δ); \|e^{At}\| ≤ e^{\|A\|t} entrywise proved | `correct` |
| `Eq. 14` | e^{Ht} = Σ_{i≤η}(Ht)ⁱ/i! + E(t), E(t) ∈ [-W(t), W(t)] (15), W(t) = e^{\|H\|t} - Σ_{i≤η}tⁱ\|H\|ⁱ/i!. | n/a — restated from Althoff et al. 2011 [63, Prop. 2]; `ExpSubExpTaylorMemExpRemainderInterval` has it | `restated` |
| `Lemma III.3` | (Correction interval matrix) F(x₀) = Σ_{i=2}^η [(i^{-i/(i-1)} - i^{-1/(i-1)})δⁱ, 0]Hⁱ/i! ⊕ E(δ, x₀) gives ∀t ∈ [0, δ]: x̂_h(t) ∈ x₀ + (t/δ)(x̂_h(δ) - x₀) ⊕ ‖x₀‖V F e₁ (16). | [`CorrectionSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Definitions/CorrectionSet.lean), [`ExpDiffMemCorrectionSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ExpDiffMemCorrectionSet.lean), [`InterpMemCorrection.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/InterpMemCorrection.lean) — F as the set of matrices it holds, η ≥ 1, δ > 0; e^{Ht} - I - (t/δ)(e^{Hδ} - I) ∈ F, then (16) from ‖x₀‖Ve₁ = x₀ | `correct` |
| `Thm. III.2` | (Solution for time intervals) R_h([0, δ]) = ⋃_{t∈[0,δ]} R_h(t) ⊆ conv(X₀, R_h(δ)) ⊕ N, N = ‖c‖V(c)F(c)e₁ ⊕ ⊕ᵢ ‖g⁽ⁱ⁾‖V(g⁽ⁱ⁾)F(g⁽ⁱ⁾)e₁. | [`TimeIntervalSubset.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/TimeIntervalSubset.lean), [`PrintedTimeIntervalCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PrintedTimeIntervalCounterexample.lean) — the enclosure with `N = N⁽⁰⁾ ⊕ ⊕ᵢ [-1, 1]N⁽ⁱ⁾`, from (3) at `c` and each `g⁽ⁱ⁾` and `Lemma III.3`'s correction sets, `R_h(δ)` as in `Thm. III.1` with one bound per vector; **Counterexample:** `Krylov.printed_time_interval_counterexample` | `fixed` — the printed `N` drops the `[-1, 1]` in front of `‖g⁽ⁱ⁾‖V(g⁽ⁱ⁾)F(g⁽ⁱ⁾)e₁` on the claim that `F(g⁽ⁱ⁾)` is symmetric; its entries `[(i^{-i/(i-1)} - i^{-1/(i-1)})δⁱ, 0]` are not, and `e^{A/2}(e₃ - e₁)` escapes for the `3 × 3` shift; see Findings |
| `Lemma IV.1` | (Krylov error of constant input solution) With Ṽ(u), H̃(u) from Alg. 1 for C = [A u; 0 0], v = [0ₙ; 1]: ∫₀^δ e^{At}dt u ∈ PṼ(u)e^{H̃(u)δ}e₁ ⊕ [-1, 1]ⁿε̃_norm δ, P = [I 0ₙ]. | [`Augment.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Operations/Augment.lean), [`ExpAugmentMulVec.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ExpAugmentMulVec.lean), [`InputSolutionMemBox.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/InputSolutionMemBox.lean) — `P e^{C̃δ}[0ₙ; 1] = ∫₀^δ e^{At}dt u` proved from the series of `C̃ = [A u; 0 0]`, and the box from (3) at `C̃`, `[0ₙ; 1]` as hypothesis, as for `Lemma III.1` | `correct` |
| `Cor. IV.1` | (Input solution for general time bounds) ∫_{t₀}^{t_e} e^{A(δ-t)}dt u ∈ PṼ(u)(e^{H̃(u)(δ-t₀)} - e^{H̃(u)(δ-t_e)})e₁ ⊕ [-1, 1]ⁿε̃_norm(t_e - t₀). | [`PartialInputSolutionMemBox.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PartialInputSolutionMemBox.lean), [`PartialInputSolutionCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PartialInputSolutionCounterexample.lean) — with the error radius `ε̃_norm((δ - t₀) + (δ - t_e))`, from `Lemma IV.1` at `δ - t₀` and at `δ - t_e`; **Counterexample:** `Krylov.partial_input_solution_counterexample` | `fixed` — the difference of `Lemma IV.1`'s two error boxes has the sum of their radii, not `ε̃_norm(t_e - t₀)`; at `A = 3`, `u = 4`, `δ = 1`, `ξ = 1`, `[t₀, t_e] = [0, 1/9]` the printed box is too small; see Findings |
| `Thm. IV.1` | (Reachable set for constant inputs) ∫₀^δ e^{A(δ-t)}dt U ⊆ (c̃_u, g̃⁽¹⁾_u, …) ⊕ [-1, 1]ⁿ(ε̃_norm(c_u) + Σε̃_norm(g⁽ⁱ⁾_u))δ for the zonotope U. | [`ImageSubsetOfApprox.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ImageSubsetOfApprox.lean) — the linear map ∫₀^δ e^{At}dt (`expIntegral`), from Lemma IV.1's box at c_u and at each g⁽ⁱ⁾_u, taken as hypotheses | `correct` |
| `Thm. IV.2` | (Reachable set for varying inputs) R_p(δ) ⊆ P(⊕_{j=1}^η {Ṽ(u)H̃ʲ(u)/j! \| u ∈ U}δʲ ⊕ {Ẽ(δ, u) \| u ∈ U})e₁ ⊕ [-1, 1]ⁿ{ε̃_norm(u) \| u ∈ U}δ. | — partial: [`PartialInputSolutionMemBox.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PartialInputSolutionMemBox.lean) (`Cor. IV.1` corrected, the per-interval step of Appendix A), [`AugmentArnoldiPow.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/AugmentArnoldiPow.lean) (P Ṽ(u)H̃ʲ(u)e₁ = A^{j-1}u for 1 ≤ j < ξ), [`ConvexKrylovTermSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ConvexKrylovTermSet.lean) (so P D⁽ʲ⁾e₁ = A^{j-1}U/j! is convex below the Krylov order, and the merge (29) holds there), [`InputReachSubsetKrylovTaylor.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/InputReachSubsetKrylovTaylor.lean) (R_p(δ) ⊆ ⊕_{j=1}^{η+1} P D⁽ʲ⁾e₁δʲ ⊕ R for arbitrarily varying inputs in a convex, closed, bounded U, η + 1 < ξ, with R the thesis' remainder E(δ)δU closed and convexified); missing: the printed remainder P{Ṽ(u)Ẽ(δ, u)}e₁ ⊕ [-1, 1]ⁿ{ε̃(u)}δ for varying inputs — its proof sums `Cor. IV.1` over l → ∞ sub-intervals (31), whose error radii add up to about lδε̃, not ε̃δ, and (3) bounds constant inputs only; the statement also drops the Ṽ(u) in front of Ẽ(δ, u) | — |
| `Cor. IV.2` | (Varying inputs with zonotopic bounds) For the zonotope U, R_p(δ) is enclosed by (c̃_u, g̃⁽ⁱ'ʲ⁾_u) ⊕ R_{p,err}, the generators PṼ(g⁽ⁱ⁾_u)H̃ʲ/j! δʲe₁. | — partial: [`AugmentArnoldiPow.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/AugmentArnoldiPow.lean) (the generators P Ṽ(g⁽ⁱ⁾_u)H̃ʲe₁ = A^{j-1}g⁽ⁱ⁾_u and the center terms P Ṽ(c_u)H̃ʲe₁ = A^{j-1}c_u for j < ξ, linear in the input, as the proof's splitting of {Ṽ(u)H̃ʲ(u) \| u ∈ U} into center and generators needs); missing: the enclosure, which rests on `Thm. IV.2`'s remainder; for η ≥ ξ the splitting itself is unsupported | — |
| `Eq. 20` | R_h(τ_{k+1}) = e^{Aδ}R_h(τ_k), R_p(τ_{k+1}) = e^{Aδ}R_p(τ_k) ⊕ R_p(τ₀) (21); with R_b, R_b(τ_{k+1}) = e^{Aδ}R_b(τ_k) (22), R_p(τ_{k+1}) = R_p(τ_k) ⊕ box(R_b(τ_{k+1})) (23). | n/a — restated from Girard 2005 [22, Alg. 1] and Girard, Le Guernic, Maler 2006 [65] | `restated` |
| `Eq. 24` | R_b(τ_{k+1}) = e^{At_k}R_b(τ₀), the propagation of (22) in one step. | n/a — e^{At_k} = (e^{Aδ})^k, Mathlib's `NormedSpace.exp_nsmul` | `mathlib` |
| `Alg. 2` | (Compute R([0, t_f])) Thm. III.1 for R*_{h,k+1} and R*_{b,k+1}, R_{p,k+1} = R_{p,k} ⊕ box(R*_{b,k+1}), Thm. III.2 for R_{h,k+1}, R_{k+1} = R_{h,k+1} ⊕ R_{p,k+1}, from Cor. IV.2 and box(conv(0ₙ, R*_{b,1})). | — partial: [`ImageSubsetOfApprox.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ImageSubsetOfApprox.lean) (`Thm. III.1`, lines 1, 7, 8), [`TimeIntervalSubset.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/TimeIntervalSubset.lean) (`Thm. III.2` corrected, lines 4, 10), [`InputReachSubsetSumExpImage.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/InputReachSubsetSumExpImage.lean) (lines 3, 8, 9 with e^{Akδ} in line 8: R_p(kδ + s) ⊆ ⊕_{i=0}^{k} e^{Aiδ}R_p(δ) for s ∈ [0, δ], 0 ∈ U), [`PrintedInputPropagationCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PrintedInputPropagationCounterexample.lean) (line 8 as printed, e^{A(k+1)δ}, misses a reachable point at t = 2δ); missing: the input solution of line 2 (`Cor. IV.2`) and the loop with its union (line 13) | — |
| `Sec. V-B` | Complexity O((o_h + o_b)n³) without and O(ξ²(o_h + o_b)n² + sξ(o_h + o_b)n³) with the Krylov subspace (Table I). | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Sec. VI` | Benchmarks and the bridge model (Tables II, Figs. 4-5). | n/a — experiments | `not-a-claim` |
| `Eq. 32` | (A-posteriori bound at t_f) ‖e^{Ct_f}v - ‖v‖Ve^{Ht_f}e₁‖ ≤ ‖v‖h_{ξ+1,ξ} max_{[0,t_f]}\|e_ξᵀe^{Ht}e₁\|(e^{ν(C)t_f} - 1)/ν(C). | n/a — restated from Wang and Ye [58, Eq. 4.1] | `restated` |
| `Prop. B.1` | The bound (3) holds with ε_norm = h_{ξ+1,ξ}ωϕ, ω = maxₖ ωₖ ≥ max_{[0,t_f]}\|e_ξᵀe^{Ht}e₁\| (35), ϕ = (e^{νt_f} - 1)/(νt_f) for ν > 0, else 1 (34). | [`ErrorLeLinear.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeLinear.lean) — from (32) at every T ∈ [0, t_f] (read as T at ν = 0, its limit) and any ω above the maximum; ω's matrix-zonotope enclosure [73] is not formalized | `proof-gap` — the monotonicity of ϕ(t) = (e^{νt} - 1)/(νt) is argued from ϕ̇ ∈ ν]0, 0.5]e^{νt}, which fails for ν < 0 (at νt = -10, ϕ̇/ν ≈ 0.0100 against 0.5e^{-10} ≈ 2.3·10⁻⁵); ϕ ≤ 1 there follows from x + 1 ≤ eˣ instead; see Findings |

## Findings

**`Thm. III.2` — the dropped `[-1, 1]`.** The proof arrives at
`⋃_{x₀∈X₀} ‖x₀‖V(x₀)F(x₀)e₁ ⊆ ‖c‖V(c)F(c)e₁ ⊕ ⨁ᵢ [-1, 1]‖g⁽ⁱ⁾‖V(g⁽ⁱ⁾)F(g⁽ⁱ⁾)e₁` and removes the
`[-1, 1]` because "all entries of `F(g⁽ⁱ⁾)` have symmetric bounds". They do not: the Taylor
terms of `F` have coefficients in `[(i^{-i/(i-1)} - i^{-1/(i-1)})δⁱ, 0]`, one-sided, so a generator
taken with a negative coefficient bends the trajectory the way `F(g⁽ⁱ⁾)` cannot. For the shift
`Ae₁ = e₂`, `Ae₂ = e₃`, `Ae₃ = 0`, `X₀ = (e₃, e₁)`, `δ = 1`, `η = 2`, Alg. 1 is exact (`V(e₁) = I`,
`H(e₁) = A`, `h₄,₃ = 0`; at `e₃` it breaks down at once), every `ε_norm` is `0`, and
`F(e₁)e₁ = λ₂e₃/2` with `λ₂ ∈ [-1/4, 0]` (`|A|³ = 0`, so `E = 0`). `X₀` and `R_h(1)` lie on the
plane `x₃ - x₂/2 = 1`, `N` on its side `≤ 0`, and `e^{A/2}(e₃ - e₁) = (-1, -1/2, 7/8)` has
`x₃ - x₂/2 = 9/8`. The zonotope enclosure (5) of the hull that Alg. 2 computes lies in the same
plane, so the computed set misses the point too.
[`PrintedTimeIntervalCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PrintedTimeIntervalCounterexample.lean)

With the `[-1, 1]` kept the theorem holds, and the proof needs the Krylov approximation only at
`c` and the `g⁽ⁱ⁾`. The printed proof also bounds `x₀ + (t/δ)(x̂_h(δ, x₀) - x₀)` by
`conv(X₀, R_h(δ))` with `x̂_h(δ, x₀) = ‖x₀‖V(x₀)e^{H(x₀)δ}e₁`, which is not a combination of the
approximations at `c` and the `g⁽ⁱ⁾` and need not lie in `R_h(δ)`. The corrected proof writes
`e^{At}x₀` as the combination of the approximations at `c` and the `g⁽ⁱ⁾` plus their errors, at most
`(‖c‖ + Σ‖g⁽ⁱ⁾‖)ε_norm t`; that is `t/δ` times the box of `R_h(δ)`, which the hull reaches with weight
`t/δ`. [`TimeIntervalSubset.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/TimeIntervalSubset.lean)

**`Cor. IV.1` — subtracting two error boxes.** `Cor. IV.1` applies `Lemma IV.1` at `δ - t₀` and
at `δ - t_e` and writes the difference of the two error boxes as `[-1, 1]ⁿ ε̃((δ - t₀) - (δ - t_e))`.
The difference of boxes of radii `ε̃(δ - t₀)` and `ε̃(δ - t_e)` has radius `ε̃(2δ - t₀ - t_e)`; the
two errors are not one error at two times. The printed radius fails: at `n = 1`, `A = 3`, `u = 4`,
`δ = 1`, Alg. 1 with `ξ = 1` on `C̃ = [3 4; 0 0]`, `ṽ = [0; 1]` gives `Ṽ = ṽ`, `H̃ = 0`,
`h₂,₁ = 4`, so `PṼ = 0`, and Prop. B.1 at `t_f = δ` (the horizon `Lemma IV.1`'s `ε̃_norm δ` is
taken over) has `ω = 1`, `ν(C̃) = λ_max([3 2; 2 0]) = 4` and `ε̃ = e⁴ - 1`. Over `[0, 1/9]` the
printed box has radius `(e⁴ - 1)/9 ≈ 5.96`, while `∫₀^{1/9} 4e^{3(1-t)}dt ≥ 4e^{8/3}/9 ≈ 6.40`. The
error `e^{C̃s}ṽ - Ṽe^{H̃s}e₁` is linear in `s` only as a bound, and its increments are not bounded by
the slope. The sum of the radii is what the two applications of `Lemma IV.1` give.
[`PartialInputSolutionCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PartialInputSolutionCounterexample.lean),
[`PartialInputSolutionMemBox.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PartialInputSolutionMemBox.lean)

**`Prop. B.1` — the sign of ϕ̇.** The proof writes ϕ̇(t) = ν Σₙ cₙ (νt)ⁿ/n! with
cₙ = 1/(n+1) - 1/((n+2)(n+1)) ∈ ]0, 0.5] and concludes ϕ̇ ∈ ν]0, 0.5]e^{νt}. Pulling the
coefficient interval out of the sum is valid only when every term has one sign, that is for
ν > 0. For ν < 0 the sum is (xeˣ - eˣ + 1)/x² at x = νt, about 0.0100 at x = -10, while
0.5e^{-10} ≈ 2.3·10⁻⁵. What the proposition needs is still true: (e^{νt} - 1)/(νt) is the
slope of exp from 0, increasing in νt by convexity, and at most 1 for νt < 0 since
eˣ ≥ 1 + x. [`ErrorLeLinear.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeLinear.lean)

The rest is not formalized, so recorded without a class.

**`Thm. IV.2` — a proof through `Cor. IV.1`.** Appendix A sums `Cor. IV.1` over `l`
sub-intervals (31) and lets `l → ∞`; with the radii that `Lemma IV.1` supports the sum grows like
`lδε̃` and the limit does not bound `R_p(δ)`. The merge (29), `aD ⊕ bD = (a + b)D`, holds for a convex
`D`. Below the Krylov order it is: `Alg. 1` satisfies `C V e_k = V H e_k` for every column but the
last, and `H` is upper Hessenberg, so `V Hʲ e₁ = Cʲ v/‖v‖` for `j < ξ`, and at `C̃ = [A u; 0 0]`,
`ṽ = [0ₙ; 1]` this is `P Ṽ(u)H̃ʲ(u)e₁ = A^{j-1}u`: `P D⁽ʲ⁾e₁ = A^{j-1}U/j!`, a linear image of `U`.
At `j ≥ ξ` the residual `h_{ξ+1,ξ}v⁽ξ⁺¹⁾` enters and the set need not be convex. So the Taylor part
of the theorem holds for arbitrarily varying inputs as long as `η < ξ`, with the remainder of
Althoff's thesis in place of the Krylov one. The printed remainder, `P{Ṽ(u)Ẽ(δ, u)}e₁ ⊕
[-1, 1]ⁿ{ε̃(u)}δ`, is open: (3) bounds the Krylov error of constant inputs, and the error of the
varying-input tail `Σ_{k≥η} Aᵏ ∫(δ-t)ᵏ/k! u(t)dt` is not one of those errors. The printed set also
writes `Ẽ(δ, u)`, a `ξ × ξ` interval matrix, where `Ṽ(u)Ẽ(δ, u)` is meant (Appendix A carries the `Ṽ(u)`).
[`ArnoldiBasisMulVecPow.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ArnoldiBasisMulVecPow.lean),
[`ConvexKrylovTermSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ConvexKrylovTermSet.lean),
[`InputReachSubsetKrylovTaylor.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/InputReachSubsetKrylovTaylor.lean)

**`Cor. IV.2` — splitting the Krylov sets.** The proof inserts `U = (c_u, g⁽ⁱ⁾_u)` into `Thm. IV.2` and
splits `{Ṽ(u)H̃ʲ(u) | u ∈ U}` into `Ṽ(c_u)H̃ʲ(c_u) ⊕ ⨁ᵢ [-1, 1]Ṽ(g⁽ⁱ⁾_u)H̃ʲ(g⁽ⁱ⁾_u)`, as if `u ↦ Ṽ(u)H̃ʲ(u)`
were linear. After `P` and `e₁` it is, below the Krylov order (`A^{j-1}u`); for `η ≥ ξ`, and for
`{Ẽ(δ, u)}` and `{ε̃(u)}`, nothing in [1] supports the splitting.

**`Alg. 2` — the step of line 8.** Line 8 propagates the input part by `e^{A(k+1)δ}`, and line 9
adds `box(R*_{b,k+1})`, so the input part after two steps is
`box(conv(0ₙ, R*_{b,1})) ⊕ box(e^{2Aδ}R*_{b,1})`; the input solution at `2δ` is
`R*_{b,1} ⊕ e^{Aδ}R*_{b,1}`, as (21) and (22) have it with `e^{Aδ}` per step. For `ẋ = -x + u`,
`u ∈ [0, 1]`, `δ = 1`, and line 2 at its tightest, `R*_{b,1} = R_p(1) ⊆ [0, 1 - e⁻¹]`, the first is
within `[0, (1 - e⁻¹)(1 + e⁻²)] ≈ [0, 0.718]`, while the constant input `1` reaches `1 - e⁻² ≈ 0.865`
at `t = 2`; with `X₀ = {0}` the union of line 13 misses it. Line 8 with `kδ`, as (24)'s `e^{At_k}`
reads for `t_k = kδ`, encloses: `R_p(kδ + s) ⊆ ⊕_{i=0}^{k} e^{Aiδ}R_p(δ)` for `s ∈ [0, δ]`, from
[Althoff's thesis](../2010/althoff-thesis.md) (`Prop. 3.2`, `Prop. 3.3`). It is proved with `0 ∈ U`,
which `Alg. 2` does not state; that is what makes line 3's `conv(0ₙ, R*_{b,1})` hold `R_p(s)` for
`s < δ` (`R_p(s) ⊆ R_p(δ)`, the input held at `0` first). As an algorithm listing the row would be `underspecified`; it stays `—` until line 2 is.
[`PrintedInputPropagationCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/PrintedInputPropagationCounterexample.lean),
[`InputReachSubsetSumExpImage.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/InputReachSubsetSumExpImage.lean)

**Minor.** `Lemma III.3`'s proof writes E(t) - (t/δ)E(δ) with \|H\|ⁱ in place of Hⁱ at the
"(15) =" step; the bound it concludes, Σ_{i>η} δⁱ\|H\|ⁱ/i! = W(δ), holds for the true series,
as formalized. `Lemma III.1` derives the box from ‖a‖ < b where (3) gives ≤.
