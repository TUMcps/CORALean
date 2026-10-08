# Reachability of Uncertain Linear Systems Using Zonotopes

A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.

**Source:** https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=e76a36257cd743a04b4454c2c50670e47b3ca448 (the author's 15-page manuscript, read in full: text extracted with `pypdf`; the typeset Springer chapter, <https://doi.org/10.1007/978-3-540-31954-2_19>, was not reachable from the environment)  
**Inventory:** confirmed (against the manuscript; the Springer typesetting is not believed to renumber anything: the manuscript already prints the page headers `292 A. Girard` ... `298 A. Girard` of the chapter, and its only numbered items are Definitions 1-2, Lemmas 1-2, Algorithm 1 and Theorem 1)

The origin of the zonotope as a reachable-set representation, and of the order
reduction rule behind `reduceGirard`: sort the generators by `‖g‖₁ - ‖g‖∞` and box the
ones nearest an axis. The paper's own reachability algorithm (Alg. 1, with the bloating
radii of Lemmas 1-2) is not what CORA's `linearSys` runs; it is formalized as
`LinearSys.girardReach`, with its enclosure and its convergence. Two of the printed
convergence bounds are false as printed and hold with `r‖A‖` in place of `r`; see Findings.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotope) Z = {c + Σ_{i=1}^p x_i g_i : -1 ≤ x_i ≤ 1}, written (c, ⟨g_1,...,g_p⟩); order p/n. | [`Zonotope.lean`](../../src/CORALean/ContSet/Zonotope/Real/Zonotope.lean) | `correct` |
| `Sec. 2` | Zonotopes are closed under linear maps, L(c, ⟨g_i⟩) = (Lc, ⟨Lg_i⟩), and under Minkowski sum, by concatenating the generator lists. Stated in prose, with no number. | [`Map.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Map.lean), [`MapExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MapExact.lean), [`Plus.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Plus.lean), [`PlusExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PlusExact.lean) | `correct` |
| `Def. 2` | (Hausdorff distance) d_H(S_1,S_2) = max(sup inf ‖x_1 - x_2‖, sup inf ‖x_1 - x_2‖). | n/a — the Hausdorff distance, which Mathlib has as `Metric.hausdorffDist` | `mathlib` |
| `Lemma 1` | (Conservative approximation of Φ_r) For a zonotope Z, Φ_r(Z) ⊆ e^{rA}Z + □(β_r), with β_r = (e^{r‖A‖} - 1)/‖A‖ · µ, and the Hausdorff distance of the two is at most µ‖A‖e^{r‖A‖}r². | [`IntegralReachSetSubsetMtimesPlusCube.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IntegralReachSetSubsetMtimesPlusCube.lean), [`HausdorffDistIntegralReachSetMtimesPlusCubeLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDistIntegralReachSetMtimesPlusCubeLe.lean), [`NormLeOfMemInputReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/NormLeOfMemInputReach.lean), [`ExistsMemInputReachDistLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsMemInputReachDistLe.lean), [`NormMulNormExpIntegralSubLe.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/NormMulNormExpIntegralSubLe.lean), [`Cube.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Cube.lean), [`CubeExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/CubeExact.lean) — `Φ_r(Z)` is `integralReachSet` on `[0, r]` (solutions in Carathéodory's sense, the input measurable), `□(β_r)` is `Zonotope.cube`, the norms are the infinity norm and its induced matrix norm, as in the paper; both halves as printed, at `0 < ‖A‖` | `underspecified` — β_r divides by ‖A‖, so `‖A‖ > 0` is supplied (at `A = 0` the radius is `rµ`) |
| `Lemma 2` | (Conservative approximation of R_[0,r]) With P the zonotope of eq. 5, R_[0,r](Z) ⊆ P + □(α_r + β_r), and the Hausdorff distance of the two is bounded by r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r) sup_{x∈Z}‖x‖). | [`IUnionIntegralReachSetSubsetLinCombPlusCube.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IUnionIntegralReachSetSubsetLinCombPlusCube.lean), [`HausdorffDistIUnionIntegralReachSetLinCombPlusCubeLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDistIUnionIntegralReachSetLinCombPlusCubeLe.lean), [`ExistsMemIUnionIntegralReachSetDistLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsMemIUnionIntegralReachSetDistLe.lean), [`ExistsLtHausdorffDistIUnionIntegralReachSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsLtHausdorffDistIUnionIntegralReachSet.lean), [`GirardExampleSpec.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/GirardExampleSpec.lean), [`NormExpMulVecSubInterpolateLe.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/NormExpMulVecSubInterpolateLe.lean), [`ExpSubOneSubLeSqMulExp.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpSubOneSubLeSqMulExp.lean), [`MemLinCombMtimesIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MemLinCombMtimesIff.lean) — P is `Zonotope.linComb Z (e^{rA}Z)`; the enclosure as printed, the convergence with `(1/2 + r‖A‖)` for the printed `(1/2 + r)`, and the counterexample to the printed bound; `sup ‖x‖` is any bound on Z's norms, the supremum the least | `fixed` — the printed bound is false (`x' = 100x`, `Z = [0,2]`, `r = 1/100`: distance ≥ 3e - 5, bound 1.02e); true with `(1/2 + r‖A‖)`; see Findings |
| `Alg. 1` | Approximating the reachable set of x' = Ax + u, ‖u‖ ≤ µ: initialise R_0 = P_0 + □(α_r + β_r), then repeat Q_i = e^{rA}Q_{i-1} + □(β_r), R_i = R_{i-1} ∪ Q_i. | [`GirardReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/GirardReach.lean), [`GirardReachEq.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/GirardReachEq.lean), [`GirardReachOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/GirardReachOuter.lean), [`IsLUBNormFoldMaxAbsBound.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IsLUBNormFoldMaxAbsBound.lean) — one `let` per printed line, the union returned as the list of the `Qᵢ`; `sup_{x∈I}‖x‖` computed exactly as the largest coordinate reach; its enclosure is `Thm. 1` | `underspecified` — the listing returns `R_N` while its loop and Thm. 1 end at `R_{N-1}` (returned here), assumes `T/r` an integer (`N = ⌈T/r⌉` here) and divides by ‖A‖ |
| `Thm. 1` | (Conservative approximation of R_[0,T](I)) The set R_{N-1} computed by Alg. 1 contains R_[0,T](I), and is within r‖A‖e^{‖A‖T}(2µ/‖A‖ + (1/2 + r) sup_{x∈Z}‖x‖) of it in Hausdorff distance. | [`GirardReachOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/GirardReachOuter.lean), [`HausdorffDistGirardReachLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDistGirardReachLe.lean), [`ExistsLtHausdorffDistGirardReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsLtHausdorffDistGirardReach.lean), [`IntegralReachSetAddEq.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IntegralReachSetAddEq.lean) — the enclosure as printed, at any `T` and `r > 0`; the convergence at `T = N r` with `(1/2 + r‖A‖)`, the printed `sup_{x∈Z}` read as `sup_{x∈I}`; the printed bound fails at `N = 1` on Lemma 2's counterexample | `fixed` — the printed bound inherits Lemma 2's error and is false; true with `(1/2 + r‖A‖)`, still `O(r)`; see Findings |
| `Sec. 3.4` | The order reduction step: of the (m+1)n generators of Q_{i+1}, sorted by ‖g‖₁ - ‖g‖∞, the 2n smallest are replaced by the n axis-aligned generators of their interval hull Σ\|h^j_i\|, which contains them. Stated in prose, with no number. | [`GirardSplit.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/GirardSplit.lean), [`ReduceGirard.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceGirard.lean), [`ReduceGirardOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceGirardOuter.lean) — at any target order `o`, and the over-approximation is proved at every partition (`reduceBy_outer`), the metric choosing only which generators to box. **As printed:** the paper's step from order `m + 1` to `m` is `o = m`, where of the `(m+1)n` generators `reduceGirard` keeps the `(m-1)n` it ranks first by `‖g‖₁ - ‖g‖∞` and boxes the `2n` smallest into `n` axis-aligned ones | `correct` |

## Findings

**Lemma 2 and Theorem 1 — the convergence bounds.** Lemma 2 prints
`d_H(R_[0,r](Z), P + □(α_r + β_r)) ≤ r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r) sup_{x∈Z} ‖x‖)`, with
"αr = (e^{r‖A‖} − 1 − r‖A‖) sup_{x∈Z} ‖x‖" and "βr = (e^{r‖A‖} − 1)/‖A‖ µ" verbatim, `‖·‖`
"the infinity norm on Rⁿ" for vectors, `‖u(t)‖ ≤ µ`, and `d_H` of Definition 2 in that norm.
The proof bounds `2α_r + β_r` by `e^{r‖A‖}r² sup ‖x‖ + e^{r‖A‖}rµ`, but `α_r` is of order
`(r‖A‖)²`, not `r²`: `2α_r ≤ e^{r‖A‖}r² sup ‖x‖` fails whenever `‖A‖ > 1` and `r` is small.
The statement fails with it. Take `x' = 100x + u`, `µ = 0`, `Z = (1, ⟨1⟩) = [0, 2]`,
`r = 1/100`. In one dimension every `p`-norm, and every induced matrix norm, is the absolute
value, so the choice of norm does not enter: `‖A‖ = 100`, `r‖A‖ = 1`,
`sup_{x∈Z} |x| = 2`, `α_r = 2(e - 2)`, `β_r = 0`, `P = [1 - e, 2e]`. The lemma's hypotheses
are only the system, `µ ≥ 0`, `r > 0` and a zonotope `Z`, and nothing here strains them. The
sets compared are the lemma's own: `R_[0,r](Z) = {e^{100t}z : t ∈ [0, r], z ∈ [0, 2]} ⊆ [0, ∞)`
and `P + □(α_r) ∋ 5 - 3e`, so `d_H ≥ 3e - 5 ≈ 3.15 > 1.02e ≈ 2.77`, the printed bound
(`exists_lt_hausdorffDist_iUnion_integralReachSet`, on `girardExample_spec`). `µ = 0` is not
what breaks it: for `µ > 0` the lower end of `R_[0,r](Z)` drops by `β_r` exactly as the
enclosure's does, the distance stays `3e - 5`, and the bound `e(µ/100 + 1.02)` stays
below it for `µ < 14`; the Lean counterexample is at `µ = 0`. Theorem 1 at `N = 1`, `T = r`,
is the same statement with `2µ` for `µ`, so it fails on the same system
(`exists_lt_hausdorffDist_girardReach`). The proof goes through with the factor corrected:
`2α_r ≤ (r‖A‖)²e^{r‖A‖} sup ‖x‖` (`exp_sub_one_sub_le_sq_mul_exp`) gives
`r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r‖A‖) sup ‖x‖)` for Lemma 2 and
`r‖A‖e^{‖A‖T}(2µ/‖A‖ + (1/2 + r‖A‖) sup ‖x‖)` for Theorem 1, both proved. The correction is
a constant, dimensionally the right one (`r‖A‖` is unitless, `r` a time), and leaves the
conclusion intact: for fixed `A` and `T` the bound is still `O(r)`, so the algorithm still
converges as the step shrinks. Theorem 1 also prints `sup_{x∈Z}` with `Z` undefined there;
it is read as `I`. [`ExistsLtHausdorffDistIUnionIntegralReachSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsLtHausdorffDistIUnionIntegralReachSet.lean), [`ExistsLtHausdorffDistGirardReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsLtHausdorffDistGirardReach.lean), [`HausdorffDistIUnionIntegralReachSetLinCombPlusCubeLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDistIUnionIntegralReachSetLinCombPlusCubeLe.lean), [`HausdorffDistGirardReachLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDistGirardReachLe.lean)

**Alg. 1 — the returned set.** The listing loops `i ← 1 to N − 1` and then returns `R_N`,
which it never computes; Theorem 1 is about `R_{N-1}`, which `girardReach` returns. `N = T/r`
is assumed an integer; `N = ⌈T/r⌉` covers `[0, T]` either way.

**Lemma 1 — dividing by `‖A‖`.** `β_r = (e^{r‖A‖} - 1)/‖A‖ · µ` is undefined at `A = 0`, where the input alone reaches `rµ`; the formalization assumes `0 < ‖A‖` throughout, as every bound in the paper does by dividing by it. Both halves of the lemma hold as printed under it.

