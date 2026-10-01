# Reachability of Uncertain Linear Systems Using Zonotopes

A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.

**Source:** https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=e76a36257cd743a04b4454c2c50670e47b3ca448 (the author's 15-page manuscript, read in full: text extracted with `pypdf`; the typeset Springer chapter, <https://doi.org/10.1007/978-3-540-31954-2_19>, was not reachable from the environment)  
**Inventory:** confirmed (against the manuscript; the Springer typesetting is not believed to renumber anything: the manuscript already prints the page headers `292 A. Girard` ... `298 A. Girard` of the chapter, and its only numbered items are Definitions 1-2, Lemmas 1-2, Algorithm 1 and Theorem 1)

The origin of the zonotope as a reachable-set representation, and of the order
reduction rule behind `reduceGirard`: sort the generators by `‖g‖₁ - ‖g‖∞` and box the
ones nearest an axis. The paper's own reachability algorithm (Alg. 1, with the bloating
radii of Lemmas 1-2) is not what CORA's `linearSys` runs, and is not formalized; the
formalization draws on the paper for the representation, the two closure properties and
the reduction step.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotope) Z = {c + Σ_{i=1}^p x_i g_i : -1 ≤ x_i ≤ 1}, written (c, ⟨g_1,...,g_p⟩); order p/n. | [`Zonotope.lean`](../../src/CORALean/ContSet/Zonotope/Real/Zonotope.lean) | `correct` |
| `Sec. 2` | Zonotopes are closed under linear maps, L(c, ⟨g_i⟩) = (Lc, ⟨Lg_i⟩), and under Minkowski sum, by concatenating the generator lists. Stated in prose, with no number. | [`Map.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Map.lean), [`MapExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MapExact.lean), [`Plus.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Plus.lean), [`PlusExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PlusExact.lean) | `correct` |
| `Def. 2` | (Hausdorff distance) d_H(S_1,S_2) = max(sup inf ‖x_1 - x_2‖, sup inf ‖x_1 - x_2‖). | n/a — the Hausdorff distance, which Mathlib has as `Metric.hausdorffDist` | `mathlib` |
| `Lemma 1` | (Conservative approximation of Φ_r) For a zonotope Z, Φ_r(Z) ⊆ e^{rA}Z + □(β_r), with β_r = (e^{r‖A‖} - 1)/‖A‖ · µ, and the Hausdorff distance of the two is at most µ‖A‖e^{r‖A‖}r². | — | — |
| `Lemma 2` | (Conservative approximation of R_[0,r]) With P the zonotope of eq. 5, R_[0,r](Z) ⊆ P + □(α_r + β_r), and the Hausdorff distance of the two is bounded by r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r) sup_{x∈Z}‖x‖). | — | — |
| `Alg. 1` | Approximating the reachable set of x' = Ax + u, ‖u‖ ≤ µ: initialise R_0 = P_0 + □(α_r + β_r), then repeat Q_i = e^{rA}Q_{i-1} + □(β_r), R_i = R_{i-1} ∪ Q_i. | — | — |
| `Thm. 1` | (Conservative approximation of R_[0,T](I)) The set R_{N-1} computed by Alg. 1 contains R_[0,T](I), and is within r‖A‖e^{‖A‖T}(2µ/‖A‖ + (1/2 + r) sup_{x∈Z}‖x‖) of it in Hausdorff distance. | — | — |
| `Sec. 3.4` | The order reduction step: of the (m+1)n generators of Q_{i+1}, sorted by ‖g‖₁ - ‖g‖∞, the 2n smallest are replaced by the n axis-aligned generators of their interval hull Σ\|h^j_i\|, which contains them. Stated in prose, with no number. | [`GirardSplit.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/GirardSplit.lean), [`ReduceGirard.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceGirard.lean), [`ReduceGirardOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceGirardOuter.lean) — at any target order `o`, not only the paper's m+1 to m step, and the over-approximation is proved at every partition (`reduceBy_outer`), the metric being only the choice of which generators to box | `correct` |
