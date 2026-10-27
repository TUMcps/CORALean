# Underapproximative Methods for the Order Reduction of Zonotopes

```bibtex
@article{luetzow2025underapproximative,
  author = {Lützow, L. and Kochdumper, N. and Althoff, M.},
  title = {Underapproximative Methods for the Order Reduction of Zonotopes},
  journal = {IEEE Control Systems Letters},
  year = {2025}
}
```

**Source:** https://publikationen.bibliothek.kit.edu/1000183724/163165215 (the published article, IEEE L-CSS vol. 9, 2025, pp. 1730-1735, doi:10.1109/LCSYS.2025.3577642, open access under CC BY 4.0 and deposited in the KIT repository; 6 pages, read in full, text extracted with `pypdf`). The paper is not on arXiv. CORA cites it in `contSet/@zonotope/reduceUnderApprox.m` as [7] for the methods `'scale'` and `'boxCone'`  
**Inventory:** confirmed (the letter numbers only Definition 1 and displays (1)-(8); the rows below are Definition 1, the displays that make a claim, and one row per method of Secs. III and IV, which the letter does not number)

A survey of four existing methods for reducing a zonotope to one of lower order whose result lies
*inside* the original (`reduced ⊆ original`), and four new ones: clustering the generators, a box
fitted to the least box-like ones, a scaled overapproximative template, and a nonlinear program. All
of them end in the same sufficient containment test (1), `Ĝ = G T` with `‖T‖∞ ≤ 1`, or in a signed
regrouping of generators, which is (1) with one `±1` per row; `Zonotope.mulGens_inner` is (1), and
every method below is an instance of it. Formalized: each method's reduction and the proof that it
is an inner approximation, the optimizers (the `k`-means++ partition, the singular value
decomposition, the second-order cone, linear and nonlinear programs) being arguments the theorem
takes with their output's property as hypothesis. The letter proves no optimality: it says (6)
"searches for the optimal underapproximation" without noting that (1) is only sufficient. (4) is
not the cosine it is said to be; see Findings.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotopes) Z = {c + Σ_{i=1}^ν λ(i) g_i : λ(i) ∈ [-1, 1]} = ⟨c, G⟩ with c ∈ ℝⁿ, G = [g_1 … g_ν] ∈ ℝ^{n×ν}; the order is o = ν/n. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Sec. II-A` | Notation: A(i,j), a(j), the matrix A\i\j without columns i and j, diag(a), sign(x) = -1 if x < 0 and 1 otherwise, the linear map AS and the Minkowski sum S_a ⊕ S_b. | n/a — notation; the sign convention is `Zonotope.dcos`'s | `not-a-claim` |
| `Sec. II-B` | (Infinity norm constraints) ‖T‖∞ ≤ α, T ∈ ℝ^{ν×ν̂}, α ≥ 0, ‖T‖∞ = max_i Σ_j \|T(i,j)\|, holds iff for every row i there are μ⁻_i, μ⁺_i ∈ ℝ^ν̂_{≥0} with t_i = Σ_j (μ⁺_i(j) - μ⁻_i(j)) e_j and Σ_j (μ⁺_i(j) + μ⁻_i(j)) = α, the containment of each row in the scaled L1 ball by the convex hull of its 2ν̂ vertices ± e_j. | [`RowSumsLeIffExistsMu.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/RowSumsLeIffExistsMu.lean) — the row sums against `α`, the equivalence in both directions | `underspecified` — the "only if" puts the slack `α - ‖t_i‖₁` on a coordinate, so `ν̂ ≥ 1` is supplied: at `ν̂ = 0` and `α > 0` the encoding reads `0 = α` while `‖T‖∞ = 0 ≤ α` |
| `Sec. II-C` | Zonotopes are closed under the linear map, A⟨c, G⟩ = ⟨Ac, AG⟩, and the Minkowski sum, ⟨c_a, G_a⟩ ⊕ ⟨c_b, G_b⟩ = ⟨c_a + c_b, [G_a G_b]⟩, which raises the order and so motivates order reduction. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Sec. II-D` | (Underapproximative order reduction) A reduction computes Ẑ = ⟨c, Ĝ⟩ ⊆ Z of order ô = ν̂/n < o with Ĝ ∈ ℝ^{n×ν̂}; the center is unchanged. Optimization-based methods maximize a measure of the volume of Ẑ under (1), heuristic ones combine generators by (2). | [`MulGens.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/MulGens.lean) — `Ĝ = G T` as `Zonotope.mulGens`, the center kept | `correct` |
| `Eq. 1` | (Sufficient containment) ∃ T ∈ ℝ^{ν×ν̂}: Ĝ = G T, ‖T‖∞ ≤ 1, and then ⟨c, Ĝ⟩ ⊆ ⟨c, G⟩. | n/a — restated; `Zonotope.mulGens_inner` has it; tracked as `Thm. 3` on [Sadraddini, Tedrake 2019](../2019/sadraddini-cdc-polytope-containment.md) | `restated` |
| `Eq. 2` | (Combining two generators) Ĝ = [G\i\j, g_i + a g_j] with a ∈ {1, -1}, which meets (1). | n/a — restated; tracked as `Prop. 6` on [Yang, Ozay 2022](../2022/yang-lcss-zonotopic-underapproximation.md) | `restated` |
| `Sec. III-A` | (Yang) Greedily combine the pair (i, j) minimizing ‖g_i‖₂ ‖g_j - (g_i/‖g_i‖₂)² g_jᵀg_i‖₂ by (2), with a = 1 if ‖H(g_i + g_j)‖₂ / ‖H(g_i - g_j)‖₂ ≥ 1 and -1 otherwise, H = G\i\jᵀ (G\i\j G\i\jᵀ)⁻¹ the right inverse, until ν̂ generators remain. | n/a — restated; tracked as `Sec. IV-B.1` on [Yang, Ozay 2022](../2022/yang-lcss-zonotopic-underapproximation.md) | `restated` |
| `Sec. III-B` | (Raghuraman) Sort the generators by 2-norm, G_s = [g_{s,1} … g_{s,ν}]; take P(j,i) = g_{s,i}ᵀ g_{s,j} for i = 1..ν̂ and j = ν̂+1..ν; Ĝ = G_s T with T(j,i) = 1 if j = i ≤ ν̂, P(j,i)/\|P(j,i)\| if j > ν̂ and \|P(j,i)\| > \|P(j,k)\| for all k ≠ i, and 0 otherwise. | [`SortByLength.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SortByLength.lean), [`SortByLengthConstruct.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SortByLengthConstruct.lean), [`SortByLengthAntitone.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SortByLengthAntitone.lean), [`ReduceUnderApproxRaghuraman.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceUnderApproxRaghuraman.lean), [`ReduceUnderApproxRaghuramanInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceUnderApproxRaghuramanInner.lean) — one `let` per printed step; the reduced zonotope lies inside `Z` | `underspecified` — at `ν̂ = 1` a small generator orthogonal to the large one has strict maximum `P = 0` and the printed `P/\|P\|` is `0/0`, read as `0`; `ν̂ ≤ ν` is supplied; ties between equal norms are broken by `Tuple.sort` |
| `Sec. III-C` | (Kochdumper) Sort as in Sec. III-B; Ĝ = [g_{s,1} … g_{s,ν̂-1}, Σ_{i=ν̂}^ν sign(g_{s,i}(1)) g_{s,i}], the first element of each generator fixing its sign in the sum. | [`ReduceUnderApproxKochdumper.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceUnderApproxKochdumper.lean), [`ReduceUnderApproxKochdumperInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceUnderApproxKochdumperInner.lean) — the sort of Sec. III-B, `n ≥ 1` for the first element, `ν̂ ≤ ν`; the reduced zonotope lies inside `Z` | `correct` |
| `Sec. III-D` | (Sadraddini) Minimize the Hausdorff distance between Z and Ẑ under (1) by (3), nonlinear through the product Ĝ T_Δ; solved by random Ĝ, a diagonal rescaling Ĝ diag(λ) = G T with ‖T‖∞ ≤ 1, then alternating linear programs in T_Δ and Ĝ. The result need not be optimal: the iteration need not converge to the optimum of (3), and (1) is sufficient but not necessary. | n/a — restated; tracked as `Cor. 6` on [Sadraddini, Tedrake 2019](../2019/sadraddini-cdc-polytope-containment.md) | `restated` |
| `Sec. IV-A` | (Clustering) Partition the generators into ν̂ clusters C_k by k-means++ with distance 1 - dcos(g_i, g_j); sum each cluster, ĝ_k = Σ_{g ∈ C_k} sign(g(1)) g; Ĝ = [ĝ_1 … ĝ_ν̂]. | [`ReduceUnderApproxCluster.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceUnderApproxCluster.lean), [`ReduceUnderApproxClusterInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceUnderApproxClusterInner.lean) — the partition is an argument, as k-means++ is randomized; the reduced zonotope lies inside `Z` for every partition | `underspecified` — Step 1 is not a function of `G`, so the partition is supplied; a zero generator makes `dcos` `0/0`; "globally optimal groupings" is not what k-means++ computes, see Findings |
| `Eq. 4` | dcos(g_i, g_j) = sign(g_i(1) g_j(1)) g_iᵀg_j / √((g_iᵀg_i)(g_jᵀg_j)), "the cosine of the angle between sign(g_i(1)) g_i and sign(g_j(1)) g_j". | [`Dcos.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Dcos.lean), [`ExistsDcosNeCosSigned.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ExistsDcosNeCosSigned.lean), [`DcosEqCosSigned.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/DcosEqCosSigned.lean) — (4) as printed; it is that cosine when both first elements are nonzero **Counterexample:** `Zonotope.exists_dcos_ne_cosSigned` | `fixed` — false when one first element is `0` and the other negative (g_i = (-1, 1), g_j = (0, 1): the cosine is -1/√2, (4) gives 1/√2); true with sign(g_i(1)) sign(g_j(1)) for sign(g_i(1) g_j(1)); see Findings |
| `Sec. IV-B` | (Box) Split Z = Z_a ⊕ Z_b with Z_a = ⟨c, G_a⟩, G_a ∈ ℝ^{n×(ν̂-n)}, by (5); rotate Z_br = Uᵀ Z_b with U from the singular value decomposition of C = [G_b -G_b][G_b -G_b]ᵀ = UΣVᵀ. Take the box B = ⟨0, diag(γ)⟩ ⊆ Z_br maximizing 2ⁿ ∏γ(i) subject to diag(γ) = G_br T, ‖T‖∞ ≤ 1 (a second-order cone program, as maximizing the concave ⁿ√∏γ(i) has the same maximizers); rotate back, UB ⊆ Z_b, Ẑ = Z_a ⊕ UB = ⟨c, [G_a U diag(γ)]⟩. | [`ReduceUnderApproxBox.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceUnderApproxBox.lean), [`ReduceUnderApproxBoxInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceUnderApproxBoxInner.lean), [`SplitKept.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SplitKept.lean), [`SplitDropped.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SplitDropped.lean), [`SplitKeptAddSplitDroppedSubset.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SplitKeptAddSplitDroppedSubset.lean), [`IsMaxOnBoxVolumeIffGeomMean.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IsMaxOnBoxVolumeIffGeomMean.lean), [`ConcaveOnGeomMean.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ConcaveOnGeomMean.lean) — `Ẑ ⊆ Z` for every orthogonal `U` and every box inside `Z_br`; the same maximizers of `2ⁿ ∏γ` and `(∏γ)^{1/n}` over any set of nonnegative `γ`; `(∏γ)^{1/n}` is concave on the nonnegative orthant | `underspecified` — `ô ≥ 1` is supplied (else `ν̂ - n` is negative); `U` and `γ` are arguments |
| `Eq. 5` | ‖g_{a,i}‖₁ - ‖g_{a,i}‖∞ ≥ ‖g_{b,j}‖₁ - ‖g_{b,j}‖∞ for all i = 1..ν̂-n and j = 1..ν_b, the split of Z_a and Z_b (Girard's metric). | [`GirardSplitMetricLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GirardSplitMetricLe.lean) — the partition `girardSplit` meets it | `correct` |
| `Sec. IV-C` | (Scale) Take Z_o = ⟨c, G_o⟩ ⊇ Z of ν̂ generators by an overapproximative order reduction; Ẑ = ⟨c, G_o diag(λ)⟩ with λ ≥ 0 maximizing Σ_i λ(i) ‖g_{o,i}‖₂ subject to G_o diag(λ) = G T, ‖T‖∞ ≤ 1 (a linear program), and then Ẑ ⊆ Z. | [`ReduceUnderApproxScale.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceUnderApproxScale.lean), [`ReduceUnderApproxScaleInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceUnderApproxScaleInner.lean) — the template and `λ` are arguments; `Ẑ ⊆ Z` follows from the constraint, for any template | `correct` |
| `Sec. IV-D` | (NLP) The maximum-volume Ẑ = ⟨c, Ĝ⟩ ⊆ Z of ν̂ generators is the solution of max volume(⟨c, Ĝ⟩) subject to (1) (6), so "this approach searches for the optimal underapproximation". For speed: split Z = ⟨c, G_a⟩ ⊕ ⟨0, G_b⟩, G_a the (ν̂-n) generators of largest 2-norm; replace ⟨0, G_b⟩ by ⟨0, Ĝ_b⟩, Ĝ_b ∈ ℝ^{n×n}, from (6), whose cost is 2ⁿ \|det Ĝ_b\|; Ẑ = ⟨c, [G_a Ĝ_b]⟩. | [`ReduceUnderApproxNLP.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceUnderApproxNLP.lean), [`ReduceUnderApproxNLPInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceUnderApproxNLPInner.lean), [`LengthSplit.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/LengthSplit.lean), [`LengthSplitLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/LengthSplitLe.lean), [`VolumeEqOfReal.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/VolumeEqOfReal.lean) — `Ẑ ⊆ Z` for any `Ĝ_b` meeting (1) against `G_b`; the split keeps the longest generators; the square cost is `2ⁿ \|det Ĝ_b\|`. No optimality is proved | `underspecified` — (6) maximizes over the sufficient condition (1), so its optimum is the maximum-volume underapproximation only if (1) is also necessary, which the letter does not argue (it notes the gap for Sadraddini's method, Sec. III-D); see Findings |
| `Eq. 7` | (Volume of a zonotope) For full-rank Ĝ, volume(⟨c, Ĝ⟩) = 2ⁿ Σ_{1 ≤ j_1 < … < j_n ≤ ν̂} \|det(Ĝ_{j_1,…,j_n})\|. | n/a — restated from Gover and Krikorian 2010 [25, Cor. 3.4]; `Zonotope.volume` is the sum, and `Zonotope.volume_eq_of_h_eq` shows it is the Lebesgue measure for `n` generators | `restated` |
| `Eq. 8` | The tightness of an underapproximation is the volume ratio R = (volumeApprox(Ẑ) / volumeApprox(Z))^{1/n}, with the exact volume (7) below dimension 10 and 150 generators and the volume of the tightest box overapproximation otherwise. | n/a — a measure for the experiments | `not-a-claim` |
| `Sec. III-IV (complexity)` | Running times with ν = on generators and ô constant: Yang O(n⁴), Raghuraman O(n³), Kochdumper O(n²), Clustering O(n³) for evaluating (4); none stated for the optimization-based methods, whose cost depends on the solver. | n/a — running times | `not-a-claim` |
| `Sec. V` | Comparison on 50 random zonotopes per dimension and order, volume ratio (8) and computation time (Figs. 1-2): NLP tightest for ô = 1 in low dimension, Kochdumper and Raghuraman fastest, Yang and Clustering the best balance, Clustering scaling to n ≥ 20 and o ≥ 200. | n/a — experiments | `not-a-claim` |
| `Sec. VI` | Conclusion: Clustering is the most practical method, NLP for order 1 when tightness matters, Kochdumper under tight computational resources. | n/a — a recommendation | `not-a-claim` |

## Findings

**Eq. (4) is not the cosine of the sign-aligned generators.** The letter defines
`sign(x) = -1` if `x < 0` and `1` otherwise (Sec. II-A) and says (4),
`dcos(g_i, g_j) = sign(g_i(1) g_j(1)) g_iᵀg_j / √((g_iᵀg_i)(g_jᵀg_j))`, "computes the cosine of the
angle between `sign(g_i(1)) g_i` and `sign(g_j(1)) g_j`". The product of the two signs is
`sign(g_i(1)) sign(g_j(1))`, but `sign(g_i(1) g_j(1))` is not that when exactly one first
element is `0` and the other negative: the product is `0`, so the printed sign is `1`, while
the signs multiply to `-1`. For `g_i = (-1, 1)`, `g_j = (0, 1)` the vectors `(1, -1)` and
`(0, 1)` have cosine `-1/√2`, and (4) gives `1/√2`
(`Zonotope.exists_dcos_ne_cosSigned`). A generator with a vanishing first element is an
ordinary input, so the row is `fixed`; with both first elements nonzero the two agree
(`Zonotope.dcos_eq_cosSigned`), and the corrected formula is
`sign(g_i(1)) sign(g_j(1)) g_iᵀg_j / √(…)`. The error enters only through the clustering
distance `1 - dcos`: the reduction itself is an inner approximation for every partition
(`Zonotope.reduceUnderApproxCluster_inner`), so the result stays sound and only its quality
suffers. Whether CORA's implementation shares the error was not checked.

**Sec. II-B: the encoding needs `ν̂ ≥ 1`.** `‖T‖∞ ≤ α` is equivalent to the `μ±` encoding
only when there is a coordinate to hold the slack `α - ‖t_i‖₁` (`ν̂ ≥ 1`); at `ν̂ = 0` the
encoding reads `0 = α`. `Zonotope.rowSums_le_iff_exists_mu`.

**Sec. III-B: `0/0` at `ν̂ = 1`.** With a single large generator the condition "`|P(j,i)| > |P(j,k)|`
for all `k ≠ i`" is vacuous, so a small generator orthogonal to it satisfies it with `P(j,1) = 0`
and the printed `P/|P|` is `0/0`. The Lean definition reads it as `0`, which drops that generator;
for `ν̂ ≥ 2` a zero `P` is never a strict maximum and the case does not arise.

**Sec. IV-A: k-means++ does not find the globally optimal grouping.** The letter motivates
`k`-means++ as finding "globally optimal groupings of aligned generators rather than relying on a
purely greedy strategy". `k`-means++ is a randomized seeding for Lloyd's algorithm, which reaches a
local optimum of the clustering cost; the partition is therefore an argument of the Lean
definition, and the theorem holds for all of them. No result of the letter depends on the sentence.

**Sec. IV-C: the template need not contain `Z`.** Step 1) takes `Z ⊆ Z_o` from an
overapproximative reduction. The inner approximation `Ẑ ⊆ Z` follows from the linear program's
constraint alone (`Zonotope.reduceUnderApproxScale_inner`), so the template may be any zonotope
of `ν̂` generators; the overapproximation only makes the result larger.

**Sec. IV-D: optimality.** The letter writes the maximum-volume underapproximation as (6), which
maximizes over (1), and concludes "this approach searches for the optimal underapproximation". For
Sadraddini's method (Sec. III-D) it notes that (1) is sufficient but not necessary, so the result
may not be optimal; the same applies to (6), whose optimum is only the best zonotope that (1)
certifies, and the letter gives no argument that the two coincide. Nothing here shows they differ
either: the claim is unproved, not disproved. The gradient method for the nonconvex (6) also
reaches only a local optimum, which the letter says. Formalized is what holds regardless:
`Zonotope.reduceUnderApproxNLP_inner`, an inner approximation for any `Ĝ_b` meeting (1).

**Sec. IV-B: `ô ≥ 1`.** `G_a` has `ν̂ - n` generators, so the method needs `ν̂ ≥ n`; the Lean
definition takes `ô` and uses `(ô - 1) n` generators for `G_a`, which at `ô = 0` is the natural
subtraction `0`.
