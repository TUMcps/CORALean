# Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed Over Bounded Regions

R. L. Smith. "Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed Over Bounded Regions". Operations Research 32(6), pp. 1296-1308, 1984.

**Source:** http://deepblue.lib.umich.edu/bitstream/2027.42/7681/5/bam4111.0001.001.pdf (University of Michigan, Deep Blue; fetched from the Internet Archive snapshot <https://web.archive.org/web/2015id_/http://deepblue.lib.umich.edu/bitstream/2027.42/7681/5/bam4111.0001.001.pdf>): the author's own Technical Report #81-1 of the same title, Department of Industrial and Operations Engineering, January 1981, revised January 1982. A scan with no text layer, so all 20 pages were rendered with PyMuPDF and read as images. The copy ends at Table 2 (report page 18): the closing section the text promises ("how large M must be"), the conclusions and the references are not in it. The journal article, <https://doi.org/10.1287/opre.32.6.1296>, was not reachable from the environment (publisher paywall).  
**Inventory:** unconfirmed (against the 1982 report, which stops at Table 2; the journal version may number, reorder or extend its items. The report's numbered items are Assumption (a), (b), Lemmas 1-2, Theorems 1-3 and Tables 1-2, with the Mixing Algorithm and three named special cases)

The paper behind CORA's `hitAndRun` sampler (`randPoint_` of `zonotope` and `conZonotope`): the *mixing algorithm* picks
a direction, finds the chord of the set through the current point, and moves to a uniform point of the chord. What is
formalized is the part of it a theorem about reals can state: the chord is `HPolytope.hitAndRunStep` and the point
it returns stays in the polytope, and the two lemmas that make the uniform law stationary and the chain indecomposable,
through Mathlib's `Kernel.Invariant`. Convergence to uniform (Theorems 1-3) needs the ergodic theory of a general-state
Markov chain, which Mathlib does not have, and is `not-covered`. CORA's coverage row for `randPoint_` is `out-of-scope`
(`random/sampling`); the formalization gives the deterministic core, not CORA's LP-based chord.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 3` | (Mixing Algorithm) Choose X₀ ∈ S; then, N times: draw a direction d uniformly over a direction set D ⊆ ℝⁿ, find the line set L = S ∩ {x = X_i + λd}, and draw X_{i+1} uniformly over L. With D the unit sphere this is the random-directions algorithm of Boneh-Golan and Smith. | [`HitAndRunStep.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/HitAndRunStep.lean), [`HitAndRunStepMem.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/HitAndRunStepMem.lean) — for S an H-polytope: L is the chord `[t̲, t̄]` of Polyak-Gryazina's Eq. 1 (exact at an interior point, `MemAddSmulIffChord`), the uniform draw is `x + (t̲ + u(t̄ - t̲))d` with `d` and `u ∈ [0, 1]` as arguments, and the returned point satisfies every inequality | `correct` |
| `Assumption` | (a) There is a measurable f(y\|x) on S × S with P(A\|x) = ∫_A f(y\|x) dy for all measurable A ⊆ S. (b) f(y\|x) > 0 for all x, y ∈ S. | [`SymmetricDensityKernelInvariant.lean`](../../src/CORALean/Global/SymmetricDensityKernelInvariant.lean), [`PositiveDensityIndecomposable.lean`](../../src/CORALean/Global/PositiveDensityIndecomposable.lean) — hypotheses of the two lemmas: a Markov kernel with `κ x A = ∫⁻ y in A, f x y ∂μ` for a measurable density, and `0 < f x y` | `correct` |
| `Lemma 1` | Under Assumption (a), the uniform distribution over S is a stationary initial distribution for the chain of a symmetric mixing algorithm: λ(A) = ∫_S P(A\|x) λ(dx), λ = V/V(S). Proof: f(y\|x) = f(x\|y) and Fubini. | [`SymmetricDensityKernelInvariant.lean`](../../src/CORALean/Global/SymmetricDensityKernelInvariant.lean) — a Markov kernel with a measurable symmetric density f with respect to an s-finite measure μ leaves μ invariant, `Kernel.Invariant κ μ`; the proof shows detailed balance (Mathlib's `Kernel.IsReversible`) by Tonelli, the interchange of the printed proof. λ is V restricted to S divided by V(S), a scalar multiple of the reference measure, and invariance scales | `correct` |
| `Lemma 2` | Under Assumption (a), (b), the chain is indecomposable: there are no two disjoint closed sets A₁, A₂ ⊆ S, a set being closed when P(Ā\|x) = 1 for all x ∈ A (A non-empty). | [`PositiveDensityIndecomposable.lean`](../../src/CORALean/Global/PositiveDensityIndecomposable.lean) — for a nonzero measure μ and a measurable density f > 0: no two non-empty disjoint measurable sets with `∫⁻ y in Aᵢᶜ, f x y ∂μ = 0` for `x ∈ Aᵢ`. The complement of a closed set is μ-null, which replaces the paper's third set Ā = S - (A₁ ∪ A₂) and its case split | `correct` |
| `Thm. 1` | Under Assumption (a), (b), λ is the unique stationary distribution of the chain of a symmetric mixing algorithm, and the chain started from λ is ergodic: (1/m) Σ_{i≤m} χ_A(X_i) → λ(A). Proof: Lemmas 1-2 and Breiman, Prop. 7.11 and Thm. 7.16. | n/a — not-covered: uniqueness of the stationary law and the ergodic theorem for an indecomposable general-state chain (Breiman) are not in Mathlib, which has `Kernel.Invariant`, `IsReversible` and `IsIrreducible` and no convergence theory. The two hypotheses it combines are Lemmas 1-2 | `not-covered` |
| `Thm. 2` | Under Assumption (a), (b), the chain is strongly mixing: P(X_m ∈ A \| X₀ = x) → λ(A) for all x ∈ S and measurable A. Proof: Doob's conditions (indecomposable, nonperiodic, absolutely continuous) on f^(n) > 0. | n/a — not-covered: Doob's strong-mixing theorem is not in Mathlib; the nonperiodicity and absolute-continuity checks are routine given Lemma 2's argument | `not-covered` |
| `Thm. 3` | For the random-directions chain on an open S ⊂ ℝⁿ, \|P(X_m ∈ A \| X₀ = x) - λ(A)\| < (1 - γ/(n 2ⁿ⁻¹))^(m-1), γ the ratio of the content of S to that of the smallest sphere containing S. Proof: Doob's case (b) bound with the density f(y\|x) = 2/(S_n(r(x,y)) d(x,y)) ≥ 1/(n 2ⁿ⁻¹ V_n(d/2)). | n/a — not-covered: Doob's quantitative bound is not in Mathlib, and the density computation is a surface-measure calculation in ℝⁿ; see Findings for the circumscribed sphere | `not-covered` |
| `Sec. 3 (Random Directions)` | The random-directions algorithm: D the unit sphere, d = N/‖N‖ for N a vector of n independent standard normals; Assumption (a), (b) hold for every open S ⊆ ℝⁿ (shown in Section 4). | — | — |
| `Sec. 3 (symmetry)` | For S open in ℝⁿ every mixing algorithm is symmetric: the probability of traveling from x to a neighborhood of y is that of traveling from y to a neighborhood of x. | — | — |
| `Sec. 3 (Coordinate Directions)` | The coordinate-directions algorithm (Telgen): D = {±eⁱ}. If the infimum of the line-set lengths is positive, the M₀-step law satisfies Assumption (a), (b) and X₀, X_{M₀}, X_{2M₀}, ... is asymptotically uniform; on a rectangular mesh the chain is finite with a symmetric, irreducible, aperiodic, doubly stochastic matrix, so P^m_{ij} → 1/N. | — | — |
| `Sec. 3 (Vertex Reaching)` | On a simple polytope with r vertices, moving along edges to adjacent vertices (f ≡ 1, λ(vᵢ) = 1/r), the number of vertices visited until a distinguished one is hit is approximately geometric, with expectation r. | — | — |
| `Sec. 4 (disk)` | For S a disk in ℝ², Thm. 3 gives (3/4)^(m-1); "we will be within 1% of a uniform distribution over S after 17 iterations of the random directions algorithm regardless of starting point". | [`SmithDiskIterations.lean`](../../src/CORALean/Global/SmithDiskIterations.lean) — `(3/4)^(17-1) > 1/100` and `(3/4)^(18-1) < 1/100` | `underspecified` — an off-by-one: the bound at 17 iterations is 1.002%, and 1% holds from 18; see Findings |
| `Sec. 4 (cube)` | For the 10-dimensional hypercube the content ratio to the circumscribed sphere is roughly 250 to 1, giving a theoretical upper bound of over five million iterations to get within 1% of uniformity (formula 2(nπ/4)^{n/2}(nΓ(n/2))⁻¹ for the sphere over the cube). | — | — |
| `Table 1` | Chi-square frequency tests (10 equal-volume slabs per coordinate, 1000 points of the random-directions algorithm in a 10-dimensional cube, every 10th of 10,000 iterates, shuffled): 7 of 10 coordinates pass at the 10% level. | n/a — an experiment | `not-a-claim` |
| `Table 2` | Chi-square serial-correlation tests (99 degrees of freedom) on the same points: 9 of 10 coordinates pass at the 10% level. | n/a — an experiment | `not-a-claim` |

## Findings

**Sec. 4 (disk) — 17 iterations.** Theorem 3 at `n = 2` and a disk, `γ = 1`, gives
`(3/4)^(m-1)` for the distance after `m` iterations. The text concludes that 1% is reached "after 17
iterations", but `m = 17` gives `(3/4)^16 = 0.010023…`, above `1/100`; the bound is below 1% from `m = 18`,
where the exponent is `17` (`smith_disk_bound_iterations`). The bound is only an upper bound, so the
chain may be within 1% earlier; what the printed bound certifies is `m ≥ 18`. [`SmithDiskIterations.lean`](../../src/CORALean/Global/SmithDiskIterations.lean)

**Thm. 3 — the circumscribed sphere.** The proof bounds the density below by
`1/(n 2ⁿ⁻¹ V_n(d/2))`, `d` the greatest distance between two points of `S`, and calls `V_n(d/2)` "the volume of a
circumscribed sphere around S". A set of diameter `d` need not fit in a ball of radius `d/2` (an
equilateral triangle needs radius `d/√3`), so `V_n(d/2)` can be smaller than the volume of the smallest enclosing
sphere. The theorem as stated, with `γ` the ratio to the smallest enclosing sphere, still follows: that sphere's
volume is at least `V_n(d/2)`, so the printed `γ` is no larger than the one the proof computes, and the bound
printed is the weaker one. The identification in the proof is what is wrong, not the statement.

**Citation numbering.** Section 2 cites "Patel and Smith [13]", and Section 3 cites "Boneh and Golan [13]" and
"Smith [13] later but independently proposed the same algorithm", while the heading of the random-directions
algorithm reads "(Boneh and Golan [13], Smith [18])". `[13]` is used for three papers; the second `Smith [13]`
is `[18]`. (The report copy ends before its reference list, so which entry is which was read off the headings.)

**Inventory.** The 1982 report copy stops after Table 2, with the "last section" on how large `M` must be and
the references missing, and the journal article was not reached, so the row set is that of the report.
