# On Computing the Minkowski Difference of Zonotopes

M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv, 2015.

**Source:** https://arxiv.org/pdf/1512.02794 (read as the PDF; its numbering agrees
exactly with the ar5iv rendering at https://ar5iv.labs.arxiv.org/html/1512.02794
this page was first read from — all seventeen locators checked against the PDF
text, Def. 1 through Prop. 6, and none differ)  
**Inventory:** confirmed

The Minkowski difference of zonotopes: exact where the generators align, and
approximated otherwise. `minkDiffAligned` is the exact case; CORA's default
`'approx'` is not followed here — see [FINDINGS.md](../../FINDINGS.md).

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Zonotope, G-Representation) Z = {c + Σ β_i g^(i) \| β_i∈[-1,1]}, order ϱ=p/n; shorthand Z=(c,g^(1),...,g^(p)). | n/a — restated from A. Girard, "Reachability of Uncertain Linear Systems Using Zonotopes", HSCC 2005, where the representation is introduced |
| `Lemma 1` | (Minkowski Difference from Finitely Many Intersections) [cites [37, Thm 2.1]] For convex subtrahend Z_s, Z_m ⊖ Z_s = ⋂_{v^(i)∈V} (Z_m - v^(i)) over the vertices V of Z_s. | — |
| `Thm. 1` | (Minkowski Difference from Generators) For zonotopes Z_m, Z_s, Z_m ⊖ Z_s can be computed by a recursive procedure using only the generators of Z_s: Z_int^(1) = Z_m - c^(s), Z_int^(i+1) = (Z_int^(i)+g^(s,i)) ∩ (Z_int^(i)-g^(s,i)), giving Z_m⊖Z_s = Z_int^(p_s+1). | [`MinkDiffGenRecExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffGenRecExact.lean) |
| `Def. 2` | (n-dimensional cross product) [cites [47]] For n-1 vectors h^(i) stored in H, nX(H) = [det(H^[1]), -det(H^[2]), ..., (-1)^{n+1}det(H^[n])]^T, where H^[i] is H with row i removed. | — |
| `Thm. 2` | (H-Representation of Zonotopes) [cites [10, Thm. 7]] Gives the halfspace representation Cx≤d of a zonotope (c,G) with p independent generators, using the normalized cross products nX of combinations of generators for C, and Δd = Σ\|C+g^(υ)\| for the offset. | — |
| `Lemma 2` | (H-Representation of Intersection of Translated Zonotopes) For Z_o=(c-h,G) and Z_t=(c+h,G), the halfspace representation of Z_o∩Z_t has the same C matrix as Thm. 2 but a d vector adjusted by Δd_trans = \|C+h\|. | — |
| `Thm. 3` | (H-Representation of the Minkowski Difference) For zonotopes Z_m=(c^(m),G^(m)) and Z_s=(c^(s),G^(s)), gives the halfspace representation Cx≤d of Z_m⊖Z_s, with the same C matrix as Thm. 2 and d adjusted by both Δd and Δd_trans. | n/a — deliberately done differently: the halfspace route is sound only for the minuend's own facet normals, and the scaling it needs is a pseudoinverse solution nothing checks. See `Zonotope Minkowski difference` in [FINDINGS.md](../../FINDINGS.md) |
| `Prop. 1` | (Zonotopes are not closed under Minkowski difference) Gives an explicit 3D counterexample zonotope pair Z_m, Z_s for which Z_m⊖Z_s is not itself a zonotope. | — |
| `Prop. 2` | (Generator removal) Gives a necessary-and-sufficient combinatorial condition (a sum of indicator terms equal to 2·C(p_m-1,n-2)) for the i-th generator of the minuend Z_m to be droppable without affecting Z_m⊖Z_s; states the O(C(p_m,n-1)·p_m²) complexity of checking this. | — |
| `Thm. 4` | (Under-Approximative G-Representation of the Minkowski Difference) Gives an under-approximating generator representation (ĉ,Ĝ) of Z_m⊖Z_s, with ĉ=c^(m)-c^(s) and Ĝ=Ĝ^(m)μ*, μ* the solution of an LP maximizing ζ^Tμ subject to Âμ≤b̂, μ≥0. | — |
| `Thm. 5` | (Over-Approximative G-Representation of the Minkowski Difference) Gives an over-approximating generator representation (c̃,G̃) analogous to Thm. 4, with μ* solving a differently-signed LP (minimizing ζ^Tμ subject to -Âμ≤-b̃, μ≥0). | — |
| `Prop. 3` | For C⊆A, {a+b \| a⊕C⊆A, b∈B} ⊆ {a+b \| a+b⊕C⊆A⊕B} — a general set-enclosure monotonicity lemma used in later proofs about combining Minkowski differences and sums. | [`MinkowskiDiffAddSubsetAdd.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffAddSubsetAdd.lean) — proved without the printed `C ⊆ A` hypothesis, which neither the paper's proof nor ours uses; `Prop. 4` keeps it in its signature for fidelity to the printed statement |
| `Prop. 4` | For Z_{m,encl}⊇Z_s, (Z_{m,encl}⊖Z_s)⊕Z_{m,rem} ⊆ (Z_{m,encl}⊕Z_{m,rem})⊖Z_s — a distributivity-type inclusion relating Minkowski difference/sum when the minuend is split into an enclosing part and a remainder. | [`MinkowskiDiffEnclSubsetAdd.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffEnclSubsetAdd.lean) |
| `Alg. 1` | (Generator Selection for Z_m) Sorts the generators of Z_m by length and greedily adds them, comparing interval-hull (box) ratios against Z_s, to build an enclosing Z_{m,encl}⊇Z_s with as few generators as possible; used by Prop. 4. | — |
| `Def. 3` | (Aligned zonotopes) Two zonotopes Z1=(c,g^(1),...,g^(p1)), Z2=(d,h^(1),...,h^(p2)) (each with no internally-aligned generators): Z1 is aligned with Z2 if every generator of Z2 is parallel (up to scaling) to some generator of Z1; if that holds both ways, the zonotopes are mutually aligned. | — |
| `Prop. 5` | (Minkowski difference for aligned generators) If Z_m is aligned with Z_s (γ_i g^(m,i) = g^(s,i) for i=1..p_s after reordering), then Z_m⊖Z_s is computed exactly as (c^(m)-c^(s), g^(m,1)-g^(s,1), ..., g^(m,ps)-g^(s,ps), g^(m,ps+1), ..., g^(m,pm)). | [`MinkDiffAlignedExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffAlignedExact.lean), the closed form itself [`MinkDiffAligned.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/MinkDiffAligned.lean) — proved with the alignment factor confined to `0 ≤ γ_i ≤ 1`, which the printed statement does not ask for and is false without (see the findings below), and at equal generator counts (`Z₁.h = Z₂.h`; the printed statement allows `p_s ≤ p_m`, padding `Z_s` with zero generators — `μ = 0` is allowed — recovers it) |
| `Prop. 6` | (Minkowski difference of two-dimensional zonotopes) Gives a closed-form zonotope (c^(m)-c^(s), Ĝ^(m)\|Ĉ+Ĝ^(m)\|^{-1}(Δd̂-Δd̂_trans)) for the Minkowski difference of two 2-dimensional zonotopes (exact, since the 2D case is always aligned/tractable). | — |

## Findings

**`Thm. 1` — eq. (8) is stated for a set, and is false off the convex ones.** The proof's
eq. (8), `A ⊖ ([-1,1] ⊗ g) = (A + g) ∩ (A − g)`, is asserted "for a set `A`". At
`A = {-1, 1} ⊆ ℝ` with `g = 1` the left side is `∅` and the right is `{0}`. The theorem
itself is untouched: every set the recursion reaches is convex, since it starts at a
zonotope and translates and intersections of convex sets stay convex. So the claim holds
and needs no extra hypothesis — convexity is carried along the induction here rather than
assumed.
[`MinkDiffGenRecExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffGenRecExact.lean)

**`Prop. 5` — the alignment factor is unconstrained, and the closed form is false
outside `[0, 1]`.** `Def. 3` lets `γ_i` be any real and `Prop. 5` inherits it. One
generator in ℝ refutes the printed statement: at `Z_m = (0, 1)` and `Z_s = (0, γ)` the
form `(0, 1 - γ)` holds the point `1 - γ`, which `-γ ∈ Z_s` carries out of `Z_m` to
`1 - 2γ` whenever `γ < 0` or `γ > 1`. So it is not the difference, nor even contained in
it: at `γ > 1` the difference is empty while the form is not, and at `γ < 0` the
subtrahend is the same set it is at `-γ` while the form lengthens the generator instead
of shortening it. Formalized with `0 ≤ γ_i ≤ 1`, which is exactly where the paper's own
`(Z_m ⊖ Z_s) ⊕ Z_s = Z_m` step holds, `|1 - γ_i| + |γ_i|` being `1` there and more
elsewhere.
[`MinkDiffAlignedNotInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffAlignedNotInner.lean)
