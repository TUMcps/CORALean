# Safety Assessment for Stochastic Linear Systems using Enclosing Hulls of Probability Density Functions

M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
Enclosing Hulls of Probability Density Functions". In Proc. of the European Control Conference
(ECC), pp. 625-630, 2009.

**Source:** https://mediatum.ub.tum.de/doc/1289123/document.pdf (the authors' copy in the TUM
repository, byte-identical to https://vmknoll82.in.tum.de/Main/Publications/Althoff2009d.pdf,
6 pages, read in full; text extracted with `pypdf`. The copy prints no venue; the venue, pages
625-630 and doi:10.23919/ecc.2009.7074473 are from the repository's record.)  
**Inventory:** confirmed (Definitions 1-4, Propositions 1-4 and Algorithm 1, each with its own
counter; equations (1)-(7); no Theorems, Lemmas or Corollaries)

CORA cites it for `@probZonotope`: a zonotope of possible means and a covariance, the
"G-zonotope with uncertain mean" that encloses every Gaussian density whose mean the zonotope
allows. Here that is `ProbZonotope`, read as the family of Mathlib's multivariate Gaussian laws,
with the density of `Prop. 1` proved from Mathlib's Gaussian Fourier integral and a change of
variables, and the sum, linear map and confidence sets proved exact on the laws.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | (System model) `ẋ = Ax(t) + u(t) + Cξ(t)`, `A` of full rank, `u(t) ∈ U` Lipschitz continuous with no known distribution, `ξ` white Gaussian noise: white Gaussian noise of uncertain mean. | — partial: [`HullPdf.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/HullPdf.lean), [`InputLaws.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/InputLaws.lean) — the solutions of (1) read through Eq. 2: for each admissible input `u` (staying in `U`, measurable) the Gaussian with mean `e^{rA}μ₀ + ∫₀ʳ e^{(r-τ)A}u(τ)dτ` (`LinearSys.closedForm`) and covariance `e^{rA}Σ₀e^{Aᵀr} + Σ_s(r)`; `LinProbSys` is the system as its three matrices; missing: the stochastic differential equation itself, the white Gaussian noise `ξ` as a process (Mathlib has no Itô integral or Wiener process, so the law of the solution is taken from Eq. 2 and not derived from (1)), the Lipschitz continuity of `u` (read as measurable) and `A` of full rank | — |
| `Eq. 2` | The solution `X(t) = e^{At}X(0) + ∫₀ᵗ e^{A(t-τ)}u(τ)dτ + ∫₀ᵗ e^{A(t-τ)}C dW`, split by superposition into `X_d`, Gaussian with `μ_d(t) = e^{At}μ(0) + ∫₀ᵗ e^{A(t-τ)}u(τ)dτ` and `Σ_d(t) = e^{At}Σ(0)e^{Aᵀt}`, and `X_s = N(0, Σ_s(t))`, `Σ_s(t) = ∫₀ᵗ e^{A(t-τ)}CCᵀe^{Aᵀ(t-τ)}dτ`. | n/a — restated from Gardiner's Handbook of Stochastic Methods, [14] in the paper, which this formalization does not draw on directly | `restated` |
| `Sec. II` | The integral is explicit if `AAᵀ = AᵀA`: with `A* = Q⁻¹AQ = diag(λ)`, `C* = Q⁻¹C`, `Σ_s = QΣ*_sQᵀ`, `[Σ*_s(t)]ᵢⱼ = (C*C*ᵀ)ᵢⱼ / (λᵢ + λⱼ) · (1 - e^{(-λᵢ-λⱼ)t})`. | [`NoiseCovariance.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/NoiseCovariance.lean), [`NoiseCovarianceDiagonal.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/NoiseCovarianceDiagonal.lean), [`NoiseCovarianceDiagonalCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/NoiseCovarianceDiagonalCounterexample.lean) — `Σ_s` entry by entry; for `A = diag(λ)` with real `λ` and `λᵢ + λⱼ ≠ 0` it is `(CCᵀ)ᵢⱼ / (λᵢ + λⱼ) · (e^{(λᵢ+λⱼ)t} - 1)`; the counterexample to the printed form **Counterexample:** `noiseCovariance_printed_counterexample` | `fixed` — the printed form is the one for the drift `-A`: in `ℝ¹` with `λ = C = t = 1`, `Σ_s = (e² - 1)/2` and the formula gives `(1 - e⁻²)/2`; see Findings |
| `Def. 1` | (Exact Reachable Set) `Rᵉ(r) = {x(r) \| x(t) is a solution of (1) ∀t ∈ [0, r], C = 0, x(0) ∈ X₀}`; `R(r) ⊇ Rᵉ(r)` and `R([0, r]) = ⋃_{t∈[0,r]} R(t)`. | [`ReachSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/ReachSet.lean) — `LinearSys.reachSet` at `T = [0, r]`, `t = r`, for `ẋ = Ax + u` | `correct` |
| `Def. 2` | (Enclosing probabilistic hull) `f̄_X(x, r) = sup{f_X(x, r) \| X(t) is a solution of (1) ∀t ∈ [0, r], u(t) ∈ U, f_X(x, 0) = f₀}`, and over a time interval `f̄_X(x, [0, r]) = sup{f̄_X(x, t) \| t ∈ [0, r]}`. | [`HullPdf.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/HullPdf.lean), [`HullPdfInterval.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/HullPdfInterval.lean) — `f̄_X(x, r)` as the supremum, over the admissible inputs `u`, of the Gaussian density at time `r` with initial `N(μ₀, Σ₀)`, mean `LinearSys.closedForm` and covariance `e^{rA}Σ₀e^{Aᵀr} + Σ_s(r)`; over `[0, r]` the supremum of these at the times of the interval | `underspecified` — the definition leaves open the initial density `f₀` (Sec. II's Gaussian here) and the class of the input signals (Eq. 1's Lipschitz `u`, measurable here as in `LinearSys.inputReach`); see Findings |
| `Sec. IV` | Zonotopes `Z = {c + Σᵢ β⁽ⁱ⁾ g⁽ⁱ⁾ \| -1 ≤ β⁽ⁱ⁾ ≤ 1}`, `Z = (c, g⁽¹…ᵖ⁾)`, of order `p/n`, the Minkowski sum of the segments `[-1, 1]g⁽ⁱ⁾`. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Def. 3` | (G-Zonotope with Certain Mean) The random variable `𝒵 = c + Σ_{i=1}^{q} N⁽ⁱ⁾(0, 1) · g̲⁽ⁱ⁾` with pairwise independent standard Gaussians `N⁽ⁱ⁾`, `𝒵 = (c, g̲⁽¹…ᑫ⁾)`. | [`GZonotopeLaw.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Definitions/GZonotopeLaw.lean) — its law: the standard Gaussian on `ℝ^q` pushed through `β ↦ c + G̲β` | `correct` |
| `Prop. 1` | (Gaussian Distribution of G-Zonotopes) The probability density function of a G-zonotope with certain mean and of order greater than one (`q > n`) is the multivariate Gaussian `f_𝒵 = (2π)^{-q/2} det(Σ)^{-1/2} exp(-½(x - c)ᵀΣ⁻¹(x - c))`, `Σ = G̲G̲ᵀ`. | [`GZonotopeLawEq.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/GZonotopeLawEq.lean), [`GZonotopeLawDensity.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/GZonotopeLawDensity.lean), [`GZonotopeLawEqWithDensity.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/GZonotopeLawEqWithDensity.lean), [`StdGaussianEqWithDensity.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/StdGaussianEqWithDensity.lean), [`GaussPdf.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Definitions/GaussPdf.lean), [`GZonotopeLawPrintedPdfCounterexample.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/GZonotopeLawPrintedPdfCounterexample.lean) — the law is Mathlib's `N(c, G̲G̲ᵀ)` for every `q`; when `det(G̲G̲ᵀ) ≠ 0` it has the density with `(2π)^{-n/2}`; the counterexample to `(2π)^{-q/2}` **Counterexample:** `gZonotopeLaw_printedGaussPdf_counterexample` | `fixed` — the normalization is `(2π)^{-n/2}`, not `(2π)^{-q/2}` (in `ℝ¹` with `q = 2` the printed function integrates to `(2π)^{-1/2}`), and `q > n` does not make `Σ` invertible, rank `n` does; see Findings |
| `Def. 4` | (G-Zonotope with Uncertain Mean) `𝒵 := Z ⊞ 𝒵̲`, `Z = (c, g⁽¹…ᵖ⁾)`, `𝒵̲ = (0, g̲⁽¹…ᑫ⁾)`: a G-zonotope whose centre is anywhere in `Z`, also written `(c, g⁽¹…ᵖ⁾, g̲⁽¹…ᑫ⁾)` or `(c, g⁽¹…ᵖ⁾, Σ)`; its enclosing probabilistic hull is `f̄_𝒵 = sup{f_𝒵 \| E[𝒵] ∈ Z}`. | [`ProbZonotope.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/ProbZonotope.lean), [`OfGenerators.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Operations/OfGenerators.lean), [`OfGeneratorsLaws.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/OfGeneratorsLaws.lean), [`Eph.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Definitions/Eph.lean) — the `(c, g, Σ)` form as the Gaussian laws `N(μ, Σ)`, `μ ∈ Z`; from probabilistic generators these are the laws of `μ + g̲N`; the hull as the supremum of the Gaussian density over the means | `correct` |
| `Eq. 4` | The sum and the linear map of G-zonotopes with uncertain mean, `𝒵₁ + 𝒵₂ = (c₁ + c₂, g⁽¹…ᵖ⁾, h⁽¹…ᑫ⁾, Σ₁ + Σ₂)` and `L𝒵₁ = (Lc, Lg⁽¹…ᵖ⁾, LΣ₁Lᵀ)`, by the rules for zonotopes and for Gaussian random variables. | [`Plus.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Operations/Plus.lean), [`PlusLaws.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/PlusLaws.lean), [`Mtimes.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Operations/Mtimes.lean), [`MtimesLaws.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/MtimesLaws.lean) — the convolutions of the summands' laws are exactly the laws of the sum, and the images of the laws under `L` exactly the laws of the image, for positive semidefinite covariances | `underspecified` — `Σ₁ + Σ₂` is the covariance of a sum of independent summands, which the paper leaves implicit; see Findings |
| `Prop. 2` | (Confidence set operator) `η(𝒵̲, m) = (0, g⁽¹…ⁿ⁾)`, `g⁽ⁱ⁾ = m · g̲⁽ⁱ⁾`, `m ∈ ℝ⁺` (eq. 5), for a zero-mean G-zonotope with `n` probabilistic generators; the set encloses its realizations with probability `erf(m/√2)ⁿ`. | [`ConfidenceZonotope.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Operations/ConfidenceZonotope.lean), [`ConfidenceZonotopeProb.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/ConfidenceZonotopeProb.lean), [`StdGaussianBox.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/StdGaussianBox.lean) — exactly, for invertible `G̲` and `m > 0`, with `erf(m/√2)` written as `P[-m ≤ N(0, 1) ≤ m]`, the identity the paper quotes as well known (Mathlib has no `erf`) | `underspecified` — the probability is `erf(m/√2)ⁿ` only for independent generators, `det G̲ ≠ 0`; at `G̲ = 0` it is `1`; see Findings |
| `Sec. V` | `η(𝒵, m) := Z + η(𝒵̲, m)` for an uncertain mean, the `γ`-confidence set at `m = γ`; outside it, in `Ψ = ℝⁿ \ η(𝒵, γ)`, only the probability `∫_Ψ f_𝒵 dx = 1 - erf(γ/√2)ⁿ` is kept. | [`Zonotope.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Operations/Zonotope.lean), [`ZonotopeProb.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/ZonotopeProb.lean) — every law with mean in `Z` puts at least `P[-γ ≤ N(0, 1) ≤ γ]ⁿ` on `η(𝒵, γ)` | `underspecified` — `𝒵` has no single density `f_𝒵`; for each mean in `Z` the probability of `Ψ` is at most, not exactly, `1 - erf(γ/√2)ⁿ`; see Findings |
| `Sec. VI` | Reachable sets for a time interval in three steps (Fig. 3): `R̂(r)` without input, the enclosing hull of `R(0)` and `R̂(r)`, its enlargement by the disturbances; `R(r) = e^{Ar}R(0)`. | n/a — restated from the papers it recalls, [12], [11], [13] and [17] there; tracked as `Alg. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Prop. 3` | (PDF-value evolution of a point) Under the map `e^{At}` the density value of a point changes by `e^{-tr(A)t}`: `f_R(x′, t) = e^{-tr(A)t} f_R(x, 0)`, `x′ = e^{At}x`; so over `t ∈ [0, r]` the values peak at `t = 0` or `t = r`. | [`GaussPdfExpMulVec.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/GaussPdfExpMulVec.lean), [`EphMtimesExp.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/EphMtimesExp.lean), [`EphMtimesExpLeMax.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/EphMtimesExpLeMax.lean), [`DetExpSmul.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/DetExpSmul.lean) — the Gaussian `N(e^{At}c, e^{At}Σe^{Aᵀt})` has at `e^{At}x` the value `e^{-tr(A)t}` times that of `N(c, Σ)` at `x` (`det Σ > 0`); the same for the hull of an uncertain-mean G-zonotope; so over `[0, r]` the values peak at `t = 0` or `t = r`; `det(e^{tA}) = e^{t tr(A)}`, which Mathlib lacks, is proved | `correct` |
| `Eq. 6` | `ΔR = (e^{Ar} - I + F) η(R(0), γ)` contains every `Δx(t) = x(t) - x(0)`, `t ∈ [0, r]`, so `η(R([0, r]), γ) ⊆ η(R(0), γ) + ΔR`; the hull without input is `R̂*([0, r]) = ΔR ⊞ R*`, `R* = R(0)` if `tr(A) > 0` and `R(r)` otherwise, and `R̂([kr, (k+1)r]) = e^{Akr} R̂([0, r])`. | — partial: [`ExpDiffMulVecMemCorrectionMatrix.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpDiffMulVecMemCorrectionMatrix.lean) — with the thesis' correction matrix `F` (`MatExp.correctionMatrix`): `Δx(t) = (t/r)(e^{Ar} - I)x(0) + F x(0)` for some `F` of the interval matrix, `t ∈ [0, r]`; missing: the printed `(t/r)(e^{Ar} - I + F)`, which scales `F` by `t/r` and takes `F` from [17], a paper this one does not define it from (the thesis' proof does not give the scaling), the inclusion `η(R([0,r]), γ) ⊆ η(R(0), γ) + ΔR` and the hull `R̂*([0, r])` with `R̂([kr, (k+1)r]) = e^{Akr} R̂([0, r])` | — |
| `Prop. 4` | (Input solution) `R̄([kr, (k+1)r]) = e^{A·kr} R̄([0, r]) + R̄(kr)` for the input `v = u + Cξ`; with `0 ∈ U`, `η(R̄([0, r]), γ) = η(R̄(r), γ) = R̄(r) + η(R̲̄(r), γ)`. | [`InputLaws.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/InputLaws.lean), [`InputLawsOver.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/InputLawsOver.lean), [`InputLawsAdd.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputLawsAdd.lean), [`InputLawsOverAdd.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputLawsOverAdd.lean), [`InputLawsOverDominated.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputLawsOverDominated.lean), [`NoiseCovariancePosSemidef.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/NoiseCovariancePosSemidef.lean) — the hull as the family of Gaussian laws of the input solution at the times of the interval: the laws over `[kr, (k+1)r]` are exactly the laws of `e^{Akr}X + Y`, `X` over `[0, r]` and `Y` an independent law at `kr` (means `inputReach_separation_eq`, covariances `noiseCovariance_add`); with `0 ∈ U` the laws over `[0, r]` have their mean among those at `r` and covariance below `Σ_s(r)` | `underspecified` — the input class (Lipschitz `u`, measurable here) and the `+`, an independent sum, are left open; `η` of an interval's hull is defined only for the representative at `r`; see Findings |
| `Alg. 1` | (Compute R) `R̄(r) = R̄(r) ⊞ R̲̄(r)`, `R([0, r]) = R̂([0, r]) + η(R̲̄(r), γ)`, and `R([kr, (k+1)r]) = e^{Ar} R([(k-1)r, kr]) + R̄(r)` for `k = 1 … ζ`. | [`EnclosingHull.lean`](../../src/CORALean/ContDynamics/LinProbSys/Operations/EnclosingHull.lean), [`EnclosingHullCov.lean`](../../src/CORALean/ContDynamics/LinProbSys/Theorems/EnclosingHullCov.lean) — one `let` per printed line, the loop as `k` iterations from `ℛ([0,r])`; the covariance after `k` iterations is `e^{Akr}Σ̂e^{Aᵀkr} + Σ_s(kr)` | `underspecified` — the listing says `h` time intervals and loops to `ζ`, takes `ℛ̂([0,r])`, `R̄(r)`, `ℛ̲(r)` from elsewhere, and the first interval's noise enters only through `η(ℛ̄(r), γ)`, a set; see Findings |
| `Eq. 7` | With the hull enclosed by polytopes of heights `h₁^max, h₂^max, …` on the confidence rings `Qᵢ = η(R, mᵢ₋₁) \ η(R, mᵢ)` (Fig. 5), the probability of the unsafe set `B` is over-approximated by `p̄ = 1 - erf(γ/√2)^{2n} + Σᵢ V(Qᵢ ∩ B)`, `V` the volume. | [`UnsafeProbLe.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/UnsafeProbLe.lean), [`UnsafeProbPrintedCounterexample.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/UnsafeProbPrintedCounterexample.lean) — `P(X ∈ B) ≤ P(X ∉ E) + Σᵢ hᵢ V(Qᵢ ∩ B)` for a density at most `hᵢ` on regions `Qᵢ` covering `E`; the counterexample to the sum without heights **Counterexample:** `unsafe_prob_printed_counterexample` | `fixed` — the volumes need the heights `hᵢ^max` as factors: for `X ~ N(0, 10⁻⁴)` and `B = η = [-0.03, 0.03]`, `p̄ = 1 - p² + 0.06 < p = P(X ∈ B)`; see Findings |
| `Sec. VI-D` | Non-Gaussian initial sets and noise are handled by enclosing them with enclosing probabilistic hulls (Fig. 6); with bounded supports inside the `γ`-confidence sets, `p̄ = Σᵢ V(Qᵢ ∩ B)`. | n/a — an outlook rather than a claim; its formula is eq. (7) without the Gaussian tail, and the `Eq. 7` finding applies to it | `not-a-claim` |
| `Sec. VII` | A two-dimensional and a five-dimensional example, and computation times up to `n = 100` (Figs. 7-9). | n/a — an experiment, not a claim to formalize | `not-a-claim` |

## Findings

**`Sec. II` — the closed form of `Σ*_s` is the one for `-A`.** With `A* = diag(λ)` the integrand
of `Σ_s(t) = ∫₀ᵗ e^{A(t-τ)}CCᵀe^{Aᵀ(t-τ)}dτ` is `(C*C*ᵀ)ᵢⱼ e^{(λᵢ+λⱼ)(t-τ)}`, which integrates to
`(C*C*ᵀ)ᵢⱼ / (λᵢ + λⱼ) · (e^{(λᵢ+λⱼ)t} - 1)`. The printed
`(C*C*ᵀ)ᵢⱼ / (λᵢ + λⱼ) · (1 - e^{(-λᵢ-λⱼ)t})` is smaller by `e^{-(λᵢ+λⱼ)t}`: it is the formula for
the Ornstein-Uhlenbeck process `dx = -Ax dt + C dW` of the handbook the paper cites, not for its own
`ẋ = Ax + …`. In `ℝ¹` with `λ = C = t = 1` the true value is `(e² - 1)/2 ≈ 3.19` and the printed
one `(1 - e⁻²)/2 ≈ 0.43`. For a stable `A` the printed variance grows without bound where the
true one converges. Proved for real eigenvalues; the paper's `Q` may be complex.
[`NoiseCovarianceDiagonalCounterexample.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/NoiseCovarianceDiagonalCounterexample.lean),
[`NoiseCovarianceDiagonal.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/NoiseCovarianceDiagonal.lean)

**`Prop. 1` — the normalization and the hypothesis.** The proof writes the joint density of the
`q` generators' coefficients, `(2π)^{-q/2} exp(-½yᵀy)`, and maps it to `𝒵 = c + G̲N`, keeping
`(2π)^{-q/2}`. The density of a Gaussian on `ℝⁿ` has `(2π)^{-n/2}`: with `n = 1`, `q = 2` and
`G̲ = [1 0]` the printed `f_𝒵` integrates to `(2π)^{-1/2} < 1`, so it is no density. The
hypothesis "order greater than one (`q > n`)" is also not what makes `Σ = G̲G̲ᵀ` invertible, which
`det(Σ)^{-1/2}` and `Σ⁻¹` need: `q > n` columns may span less than `ℝⁿ`, and `q = n`
independent ones suffice. Proved: the law is `N(c, G̲G̲ᵀ)` for every `q`, and has the density
with `(2π)^{-n/2}` whenever `det(G̲G̲ᵀ) ≠ 0`.
[`GZonotopeLawPrintedPdfCounterexample.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/GZonotopeLawPrintedPdfCounterexample.lean),
[`GZonotopeLawDensity.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/GZonotopeLawDensity.lean)

**`Eq. 4` — the sum is of independent summands.** `Σ₁ + Σ₂` is the covariance of `X₁ + X₂` only
when the summands are independent (at `X₂ = -X₁` the sum is `0`). The paper adds the homogeneous
and the input solution, which it treats as independent, and the formalization reads the sum as
the convolution of the laws.
[`PlusLaws.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/PlusLaws.lean)

**`Prop. 2` and `Sec. V` — when the probability is exact.** The cube `[-m, m]ⁿ` of coefficients
maps onto `η(𝒵̲, m)`, and the probability of the set is that of the cube, `erf(m/√2)ⁿ`, only when
`G̲` is injective; at `G̲ = 0` every realization is `0 ∈ η` and the probability is `1`. In
general it is at least `erf(m/√2)ⁿ`, which is what the confidence sets are used for. With an
uncertain mean, `f_𝒵` is not one density; for every mean in `Z` the probability of
`Ψ = ℝⁿ \ η(𝒵, γ)` is at most `1 - erf(γ/√2)ⁿ`, which is the bound the method needs.
[`ConfidenceZonotopeProb.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/ConfidenceZonotopeProb.lean),
[`ZonotopeProb.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/ZonotopeProb.lean)

**`Eq. 7` — volumes for probabilities.** The paper bounds the hull by polytopes `P₁, P₂, …` of
heights `h₁^max, h₂^max, …` over the rings `Qᵢ` and then sums `V(Qᵢ ∩ B)`, the volumes alone. A
volume is not a probability: for `X ~ N(0, σ²)` with `σ = 1/100`, `γ = 3` and `B = η = [-3σ, 3σ]`,
`p = erf(3/√2) = P(X ∈ B) ≥ 8/9` by Chebyshev's inequality, while the printed
`p̄ = 1 - p² + Σᵢ V(Qᵢ ∩ B) = 1 - p² + 0.06 < p`. With the heights as factors the bound holds:
`P(X ∈ B) ≤ P(X ∉ η) + Σᵢ hᵢ^max V(Qᵢ ∩ B)`. The same holds for `Sec. VI-D`'s formula. The paper's
`1 - erf(γ/√2)^{2n}` for the tail is kept as the hypothesis on `P(X ∉ η)`, not proved.
[`UnsafeProbPrintedCounterexample.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/UnsafeProbPrintedCounterexample.lean),
[`UnsafeProbLe.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/UnsafeProbLe.lean)

**`Def. 2` — what the supremum is over.** The hull is the supremum of the densities `f_X(x, r)` of
the solutions of (1) for the inputs `u(t) ∈ U` with `f_X(x, 0) = f₀`. The definition names no
`f₀`; Sec. II assumes a Gaussian initial state, which is what the Lean reads, with the law of
the solution taken from Eq. 2 (the stochastic process is not defined). Eq. 1's `u` is Lipschitz;
the Lean admits every measurable `u` in `U`, the class of the thesis' input reach set, for which
the supremum is the same or larger.
[`HullPdf.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/HullPdf.lean)

**`Prop. 4` — exact for the laws, the hull of an interval.** Read as a family of Gaussian laws,
the decomposition `x_s((k+1)r) = e^{Akr}x_s(r) + x_s(kr)` of its proof holds exactly: at every time
`s + kr` the laws are those of `e^{Akr}X + Y` for a law `X` at `s` and an independent law `Y` at
`kr`, the means by the separation of the input reach set and the covariances by
`Σ_s(a + b) = e^{Ab}Σ_s(a)e^{Aᵀb} + Σ_s(b)`. The `+` of G-zonotopes is that independent sum; the
printed statement does not say so, nor which input class. The proof's next step, that for `0 ∈ U`
the set for `t ∈ [0, r]` "equals" the one at `r`, holds for the means (the input reach set
grows) and in the Loewner order for the covariance (`Σ_s(r) - Σ_s(t) = e^{At}Σ_s(r-t)e^{Aᵀt}`);
`η` of the hull over an interval needs generators for it, which the paper does not give.
[`InputLawsOverAdd.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputLawsOverAdd.lean),
[`InputLawsOverDominated.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputLawsOverDominated.lean)

**`Alg. 1` — what the loop computes.** After `k` iterations the covariance is
`e^{Akr}Σ̂e^{Aᵀkr} + Σ_s(kr)`: the first interval's noise `Σ_s(r)` is absent, entering only through
the γ-confidence set `η(ℛ̄(r), γ)`, which has covariance `0` and whose complement the probability
`1 - erf(γ/√2)^{2n}` of Eq. 7 accounts for. The listing's output is `ℛ([kr, (k+1)r])` for
`k = 1…ζ`, its prose says `h` time intervals, and its inputs `ℛ̂([0,r])`, `R̄(r)` and `ℛ̲(r)` are
not defined by it. That the result encloses the hull is not a printed claim and is not proved.
[`EnclosingHullCov.lean`](../../src/CORALean/ContDynamics/LinProbSys/Theorems/EnclosingHullCov.lean)

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`Max.lean`](../../src/CORALean/ContSet/ProbZonotope/Real/Operations/Max.lean)
