# On Computing the Minkowski Difference of Zonotopes

M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv, 2015.

**Source:** https://arxiv.org/pdf/1512.02794 (read as the PDF; its numbering agrees
exactly with the ar5iv rendering at https://ar5iv.labs.arxiv.org/html/1512.02794
this page was first read from — all sixteen locators checked against the PDF
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
| `Thm. 1` | (Minkowski Difference from Generators) For zonotopes Z_m, Z_s, Z_m ⊖ Z_s can be computed by a recursive procedure using only the generators of Z_s: Z_int^(1) = Z_m - c^(s), Z_int^(i+1) = (Z_int^(i)+g^(s,i)) ∩ (Z_int^(i)-g^(s,i)), giving Z_m⊖Z_s = Z_int^(p_s+1). | — |
| `Def. 2` | (n-dimensional cross product) [cites [47]] For n-1 vectors h^(i) stored in H, nX(H) = [det(H^[1]), -det(H^[2]), ..., (-1)^{n+1}det(H^[n])]^T, where H^[i] is H with row i removed. | — |
| `Thm. 2` | (H-Representation of Zonotopes) [cites [10, Thm. 7]] Gives the halfspace representation Cx≤d of a zonotope (c,G) with p independent generators, using the normalized cross products nX of combinations of generators for C, and Δd = Σ\|C+g^(υ)\| for the offset. | — |
| `Lemma 2` | (H-Representation of Intersection of Translated Zonotopes) For Z_o=(c-h,G) and Z_t=(c+h,G), the halfspace representation of Z_o∩Z_t has the same C matrix as Thm. 2 but a d vector adjusted by Δd_trans = \|C+h\|. | — |
| `Thm. 3` | (H-Representation of the Minkowski Difference) For zonotopes Z_m=(c^(m),G^(m)) and Z_s=(c^(s),G^(s)), gives the halfspace representation Cx≤d of Z_m⊖Z_s, with the same C matrix as Thm. 2 and d adjusted by both Δd and Δd_trans. | [`MinkDiffRep.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/MinkDiffRep.lean) |
| `Prop. 1` | (Zonotopes are not closed under Minkowski difference) Gives an explicit 3D counterexample zonotope pair Z_m, Z_s for which Z_m⊖Z_s is not itself a zonotope. | — |
| `Prop. 2` | (Generator removal) Gives a necessary-and-sufficient combinatorial condition (a sum of indicator terms equal to 2·C(p_m-1,n-2)) for the i-th generator of the minuend Z_m to be droppable without affecting Z_m⊖Z_s; states the O(C(p_m,n-1)·p_m²) complexity of checking this. | — |
| `Thm. 4` | (Under-Approximative G-Representation of the Minkowski Difference) Gives an under-approximating generator representation (ĉ,Ĝ) of Z_m⊖Z_s, with ĉ=c^(m)-c^(s) and Ĝ=Ĝ^(m)μ*, μ* the solution of an LP maximizing ζ^Tμ subject to Âμ≤b̂, μ≥0. | — |
| `Thm. 5` | (Over-Approximative G-Representation of the Minkowski Difference) Gives an over-approximating generator representation (c̃,G̃) analogous to Thm. 4, with μ* solving a differently-signed LP (minimizing ζ^Tμ subject to -Âμ≤-b̃, μ≥0). | — |
| `Prop. 3` | For C⊆A, {a+b \| a⊕C⊆A, b∈B} ⊆ {a+b \| a+b⊕C⊆A⊕B} — a general set-enclosure monotonicity lemma used in later proofs about combining Minkowski differences and sums. | [`MinkowskiDiffAddSubsetAdd.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffAddSubsetAdd.lean) — proved without the printed `C ⊆ A` hypothesis, which neither the paper's proof nor ours uses; `Prop. 4` keeps it in its signature for fidelity to the printed statement |
| `Prop. 4` | For Z_{m,encl}⊇Z_s, (Z_{m,encl}⊖Z_s)⊕Z_{m,rem} ⊆ (Z_{m,encl}⊕Z_{m,rem})⊖Z_s — a distributivity-type inclusion relating Minkowski difference/sum when the minuend is split into an enclosing part and a remainder. | [`MinkowskiDiffEnclSubsetAdd.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffEnclSubsetAdd.lean) |
| `Alg. 1` | (Generator Selection for Z_m) Sorts the generators of Z_m by length and greedily adds them, comparing interval-hull (box) ratios against Z_s, to build an enclosing Z_{m,encl}⊇Z_s with as few generators as possible; used by Prop. 4. | — |
| `Def. 3` | (Aligned zonotopes) Two zonotopes Z1=(c,g^(1),...,g^(p1)), Z2=(d,h^(1),...,h^(p2)) (each with no internally-aligned generators) are aligned if generators of Z1 and Z2 are pairwise parallel up to scaling. | — |
| `Prop. 5` | (Minkowski difference for aligned generators) If Z_m is aligned with Z_s (γ_i g^(m,i) = g^(s,i) for i=1..p_s after reordering), then Z_m⊖Z_s is computed exactly as (c^(m)-c^(s), g^(m,1)-g^(s,1), ..., g^(m,ps)-g^(s,ps), g^(m,ps+1), ..., g^(m,pm)). | [`MinkDiffAligned.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/MinkDiffAligned.lean) |
| `Prop. 6` | (Minkowski difference of two-dimensional zonotopes) Gives a closed-form zonotope (c^(m)-c^(s), Ĝ^(m)\|Ĉ+Ĝ^(m)\|^{-1}(Δd̂-Δd̂_trans)) for the Minkowski difference of two 2-dimensional zonotopes (exact, since the 2D case is always aligned/tractable). | — |
