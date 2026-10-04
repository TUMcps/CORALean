# Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov Subspace

M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.

**Source:** https://arxiv.org/pdf/1712.00369 (arXiv:1712.00369v2, 5 Aug 2020, the author's version, 16 pages including Appendices A-B, read in full; text extracted with `pypdf`). The typeset IEEE article (doi:10.1109/TAC.2019.2906432) was not reachable; numbering is the arXiv version's, which has the TAC article's section-based labels. CORA's Krylov files (`linearSys/private/priv_reach_krylov.m`, `priv_initReach_Krylov.m`, `priv_inputSolution_Krylov.m`, `priv_exponential_Krylov*.m`) cite the paper without result numbers.  
**Inventory:** confirmed (Definition II.1, Lemmas III.1-III.3 and IV.1, Theorems III.1-III.2 and IV.1-IV.2, Corollaries IV.1-IV.2, Proposition B.1, Algorithms 1-2, equations (1)-(35); the rows below are the results and the numbered displays that make a claim)

Reachable sets of linear systems with several thousand states and arbitrarily varying
bounded inputs, by computing `e^{At}v` in a Krylov subspace (Arnoldi, `Alg. 1`) and carrying
the approximation error as a box. The approximation error itself is Wang and Ye's
a-posteriori bound (3), cited; here it is a hypothesis, as the brief for Krylov error bounds
asks. Formalized: the Arnoldi relation for `Alg. 1`, the error box (`Lemma III.1`), the
zonotope enclosures built from per-vector boxes (`Thm. III.1`, `Thm. IV.1`), the interval
vector bound (`Lemma III.2`), the correction matrix in the subspace (`Lemma III.3`), and the
error bound's linear-in-time form (`Prop. B.1`). The time-interval enclosure (`Thm. III.2`),
the augmented-system identity (`Lemma IV.1`) and the varying-input results built on it are
open; the printed proofs of `Thm. III.2`, `Cor. IV.1` and `Thm. IV.2` have gaps (Findings).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Alg. 1` | (Arnoldi iteration) v⁽¹⁾ = v/‖v‖; for k = 1…ξ: w = Cv⁽ᵏ⁾, h_{j,k} = w*v⁽ʲ⁾ and w := w - h_{j,k}v⁽ʲ⁾ for j = 1…k, h_{k+1,k} = ‖w‖, happy breakdown if h_{k+1,k} ≤ tol‖C‖, v⁽ᵏ⁺¹⁾ = w/h_{k+1,k}; the result is an orthogonal basis V of K_ξ and the upper Hessenberg H. | [`Arnoldi.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Operations/Arnoldi.lean), [`GramSchmidtStep.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Operations/GramSchmidtStep.lean), [`ArnoldiRelation.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ArnoldiRelation.lean) — the listing over ℝ, and the Arnoldi relation C v⁽ᵏ⁾ = Σ_{i≤k} h_{i,k}v⁽ⁱ⁾ + h_{k+1,k}v⁽ᵏ⁺¹⁾ for every column with h_{k+1,k} ≠ 0; orthogonality of V is not shown | `underspecified` — the happy breakdown (line 10) names no action; read as stopping at ξ = k, so that only columns with h_{k+1,k} ≠ 0 are formed |
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
| `Thm. III.2` | (Solution for time intervals) R_h([0, δ]) = ⋃_{t∈[0,δ]} R_h(t) ⊆ conv(X₀, R_h(δ)) ⊕ N, N = ‖c‖V(c)F(c)e₁ ⊕ ⊕ᵢ ‖g⁽ⁱ⁾‖V(g⁽ⁱ⁾)F(g⁽ⁱ⁾)e₁. | — | — |
| `Lemma IV.1` | (Krylov error of constant input solution) With Ṽ(u), H̃(u) from Alg. 1 for C = [A u; 0 0], v = [0ₙ; 1]: ∫₀^δ e^{At}dt u ∈ PṼ(u)e^{H̃(u)δ}e₁ ⊕ [-1, 1]ⁿε̃_norm δ, P = [I 0ₙ]. | — | — |
| `Cor. IV.1` | (Input solution for general time bounds) ∫_{t₀}^{t_e} e^{A(δ-t)}dt u ∈ PṼ(u)(e^{H̃(u)(δ-t₀)} - e^{H̃(u)(δ-t_e)})e₁ ⊕ [-1, 1]ⁿε̃_norm(t_e - t₀). | — | — |
| `Thm. IV.1` | (Reachable set for constant inputs) ∫₀^δ e^{A(δ-t)}dt U ⊆ (c̃_u, g̃⁽¹⁾_u, …) ⊕ [-1, 1]ⁿ(ε̃_norm(c_u) + Σε̃_norm(g⁽ⁱ⁾_u))δ for the zonotope U. | [`ImageSubsetOfApprox.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ImageSubsetOfApprox.lean) — the linear map ∫₀^δ e^{At}dt (`expIntegral`), from Lemma IV.1's box at c_u and at each g⁽ⁱ⁾_u, taken as hypotheses | `correct` |
| `Thm. IV.2` | (Reachable set for varying inputs) R_p(δ) ⊆ P(⊕_{j=1}^η {Ṽ(u)H̃ʲ(u)/j! \| u ∈ U}δʲ ⊕ {Ẽ(δ, u) \| u ∈ U})e₁ ⊕ [-1, 1]ⁿ{ε̃_norm(u) \| u ∈ U}δ. | — | — |
| `Cor. IV.2` | (Varying inputs with zonotopic bounds) For the zonotope U, R_p(δ) is enclosed by (c̃_u, g̃⁽ⁱ'ʲ⁾_u) ⊕ R_{p,err}, the generators PṼ(g⁽ⁱ⁾_u)H̃ʲ/j! δʲe₁. | — | — |
| `Eq. 20` | R_h(τ_{k+1}) = e^{Aδ}R_h(τ_k), R_p(τ_{k+1}) = e^{Aδ}R_p(τ_k) ⊕ R_p(τ₀) (21); with R_b, R_b(τ_{k+1}) = e^{Aδ}R_b(τ_k) (22), R_p(τ_{k+1}) = R_p(τ_k) ⊕ box(R_b(τ_{k+1})) (23). | n/a — restated from Girard 2005 [22, Alg. 1] and Girard, Le Guernic, Maler 2006 [65] | `restated` |
| `Eq. 24` | R_b(τ_{k+1}) = e^{At_k}R_b(τ₀), the propagation of (22) in one step. | n/a — e^{At_k} = (e^{Aδ})^k, Mathlib's `NormedSpace.exp_nsmul` | `mathlib` |
| `Alg. 2` | (Compute R([0, t_f])) Thm. III.1 for R*_{h,k+1} and R*_{b,k+1}, R_{p,k+1} = R_{p,k} ⊕ box(R*_{b,k+1}), Thm. III.2 for R_{h,k+1}, R_{k+1} = R_{h,k+1} ⊕ R_{p,k+1}, from Cor. IV.2 and box(conv(0ₙ, R*_{b,1})). | — | — |
| `Sec. V-B` | Complexity O((o_h + o_b)n³) without and O(ξ²(o_h + o_b)n² + sξ(o_h + o_b)n³) with the Krylov subspace (Table I). | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Sec. VI` | Benchmarks and the bridge model (Tables II, Figs. 4-5). | n/a — experiments | `not-a-claim` |
| `Eq. 32` | (A-posteriori bound at t_f) ‖e^{Ct_f}v - ‖v‖Ve^{Ht_f}e₁‖ ≤ ‖v‖h_{ξ+1,ξ} max_{[0,t_f]}\|e_ξᵀe^{Ht}e₁\|(e^{ν(C)t_f} - 1)/ν(C). | n/a — restated from Wang and Ye [58, Eq. 4.1] | `restated` |
| `Prop. B.1` | The bound (3) holds with ε_norm = h_{ξ+1,ξ}ωϕ, ω = maxₖ ωₖ ≥ max_{[0,t_f]}\|e_ξᵀe^{Ht}e₁\| (35), ϕ = (e^{νt_f} - 1)/(νt_f) for ν > 0, else 1 (34). | [`ErrorLeLinear.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeLinear.lean) — from (32) at every T ∈ [0, t_f] (read as T at ν = 0, its limit) and any ω above the maximum; ω's matrix-zonotope enclosure [73] is not formalized | `proof-gap` — the monotonicity of ϕ(t) = (e^{νt} - 1)/(νt) is argued from ϕ̇ ∈ ν]0, 0.5]e^{νt}, which fails for ν < 0 (at νt = -10, ϕ̇/ν ≈ 0.0100 against 0.5e^{-10} ≈ 2.3·10⁻⁵); ϕ ≤ 1 there follows from x + 1 ≤ eˣ instead; see Findings |

## Findings

**`Prop. B.1` — the sign of ϕ̇.** The proof writes ϕ̇(t) = ν Σₙ cₙ (νt)ⁿ/n! with
cₙ = 1/(n+1) - 1/((n+2)(n+1)) ∈ ]0, 0.5] and concludes ϕ̇ ∈ ν]0, 0.5]e^{νt}. Pulling the
coefficient interval out of the sum is valid only when every term has one sign, that is for
ν > 0. For ν < 0 the sum is (xeˣ - eˣ + 1)/x² at x = νt, about 0.0100 at x = -10, while
0.5e^{-10} ≈ 2.3·10⁻⁵. What the proposition needs is still true: (e^{νt} - 1)/(νt) is the
slope of exp from 0, increasing in νt by convexity, and at most 1 for νt < 0 since
eˣ ≥ 1 + x. [`ErrorLeLinear.lean`](../../src/CORALean/ContDynamics/LinearSys/Krylov/Theorems/ErrorLeLinear.lean)

The rest is not formalized, so recorded without a class.

**`Thm. III.2` — the approximation is not linear in the initial state.** The proof bounds
x₀ + (t/δ)(x̂_h(δ) - x₀) ⊕ (t/δ)E_red(δ, x₀) by conv(X₀, R_h(δ)), which needs
x̂_h(δ, x₀) ⊕ E_red(δ, x₀) ⊆ R_h(δ) for every x₀ ∈ X₀. `Thm. III.1`'s R_h(δ) is built from the
approximations at c and the g⁽ⁱ⁾, and x̂_h(δ, x₀) = ‖x₀‖V(x₀)e^{H(x₀)δ}e₁ is not their
combination; what `Thm. III.1` gives is e^{Aδ}x₀ ∈ R_h(δ), and x̂_h(δ, x₀) is only within
‖x₀‖ε_norm δ of that. N bounds ⋃_{x₀} ‖x₀‖V(x₀)F(x₀)e₁ by its values at c and the g⁽ⁱ⁾ in the
same way; the polynomial part of F is linear in x₀ (‖v‖VHⁱe₁ = Aⁱv below order ξ), the part
E(δ, x₀) is not, W depending on \|H(x₀)\|. An enclosure that also adds the box
[-1, 1]ⁿ 2(‖c‖ + Σ‖g⁽ⁱ⁾‖)ε_norm δ would follow from the exact interpolation error, which is
linear.

**`Cor. IV.1` and `Thm. IV.2` — subtracting two error boxes.** `Cor. IV.1` applies
`Lemma IV.1` at δ - t₀ and at δ - t_e and writes the difference of the two error boxes as
[-1, 1]ⁿ ε̃_norm((δ - t₀) - (δ - t_e)). The difference of boxes of radii ε̃_norm(δ - t₀) and
ε̃_norm(δ - t_e) has radius ε̃_norm(2δ - t₀ - t_e); the two errors are not one error at two
times. Appendix A sums the corollary over l sub-intervals (31) and lets l → ∞; with the
larger radius the sum grows like lδε̃_norm and the limit does not bound R_p(δ). The theorem's
other terms are those of the classical input enclosure (for η below the Krylov order,
PṼH̃ʲe₁ = A^{j-1}u), so `Thm. IV.2` may well hold; its printed proof does not show the Krylov
error term.

**Minor.** `Lemma III.3`'s proof writes E(t) - (t/δ)E(δ) with \|H\|ⁱ in place of Hⁱ at the
"(15) =" step; the bound it concludes, Σ_{i>η} δⁱ\|H\|ⁱ/i! = W(δ), holds for the true series,
as formalized. `Lemma III.1` derives the box from ‖a‖ < b where (3) gives ≤.
