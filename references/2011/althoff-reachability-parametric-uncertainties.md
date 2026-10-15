# Analyzing Reachability of Linear Dynamic Systems with Parametric Uncertainties

M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic
Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.), Modeling, Design,
and Simulation of Systems with Uncertainties, Springer, 2011.

**Source:** https://mediatum.ub.tum.de/doc/1287218/358815.pdf — this is the authors' own preprint/self-archived copy of the chapter (freely hosted on mediaTUM), NOT the final Springer-typeset book chapter (which is paywalled and was not accessed). Read directly with a custom PDF-content-stream text extractor since no PDF rasterizer was available in this environment (poppler/pdftoppm not installed).  
**Inventory:** confirmed (against the preprint) — but with an UNVERIFIED section-number correspondence to the published book chapter (see notes)

Cited for the matrix zonotope itself (Eq. 8) and for one construction built on
it, the matrix zonotope acting on a zonotope (`mtimesMatZonotope`, Eq. 10). CORA
cites the book; the results are in this chapter of it, which is what the entry
now names.

The typeset chapter is paywalled, so the rows below are read off the authors'
own preprint, whose local §4.1 is the book's §4.4.1 — the section our tree used
to cite, now narrowed to the equation inside it. The same construction is Prop. 3.5 of
[Althoff's thesis](../2010/althoff-thesis.md).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 8` | (Matrix Zonotope) A_Z = {G^(0) + Σ_{i=1}^κ p_i G^(i) \| p_i∈[-1,1], G^(i)∈R^{n×n}}; shorthand A_Z=(G^(0),G^(1),...,G^(κ)); order ϱ=κ/n. | [`Zonotope.lean`](../../src/CORALean/ContSet/Zonotope/Real/Zonotope.lean) — no separate `MatZonotope` type is needed: the file's own docstring states that `Zonotope (Mat ℝ m n)` *is* CORA's matrix zonotope, a center plus a bounded combination of generators being indifferent to the ambient type, so Eq. 8 is this structure instantiated at `Mat ℝ n n`. | `correct` |
| `Eq. 9` | Matrix zonotopes can equivalently be represented as the convex hull of their matrix vertices V^(i): A_Z = {Σ α_i V^(i) \| α_i∈R, α_i≥0, Σα_i=1}. | [`ZonotopeVPolytopeExact.lean`](../../src/CORALean/ContSet/Conversion/Real/Theorems/ZonotopeVPolytopeExact.lean) — `Zonotope.vPolytope_exact`, the equality Eq. 8's own generic type needs to state Eq. 9: `Zonotope.vPolytope` names the `2ʰ` sign corners as the matrix vertices V^(i) (a superset of the minimal vertex set Eq. 9 quantifies over, which changes nothing about the convex hull), and `vPolytope_exact` is `Z.construct = Z.vPolytope.construct` at any real module, in particular `Mat ℝ n n`. | `correct` |
| `Eq. 10` | (Matrix Zonotope Product) Gives the multiplication A_Z ⊗ B_Z of two matrix zonotopes A_Z=(G^(0),...,G^(κA)) and B_Z=(H^(0),...,H^(κB)), enclosed by the zonotope (G^(0)H^(0), G^(0)H^(1), ..., G^(κA)H^(κB)) obtained by pairwise-multiplying center/generator matrices. | [`MtimesMatZonotope.lean`](../../src/CORALean/ContSet/ZonoBundle/Real/Operations/MtimesMatZonotope.lean), [`MtimesMatZonotope.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/MtimesMatZonotope.lean) — both linked operations are the vector-zonotope (n×1) case, a matrix zonotope acting on a vector (or `ZonoBundle`) zonotope, not the matrix×matrix product Eq. 10 states | `correct` |
| `Prop. 3` | (Dependent Matrix Zonotope Evaluation) The set {I + At + 0.5(At)² \| A∈A_Z} (the exact quadratic Taylor term of the matrix exponential for A in a matrix zonotope A_Z) is enclosed by the smallest possible zonotope W_Z(t)=(L^(0)(t),...,L^(κW)(t)), with explicit closed-form generator matrices L^(j)(t) built from products G^(i)G^(j)+G^(j)G^(i) — this exploits the dependency between repeated occurrences of the same matrix generator (rather than treating A_Z⊗A_Z as an independent product) to get a tighter, exact-for-second-order enclosure. | [`QuadTaylor.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/QuadTaylor.lean), [`QuadTaylorOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/QuadTaylorOuter.lean), [`QuadTaylorPrinted.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/QuadTaylorPrinted.lean) — `Zonotope.quadTaylor`/`quadTaylor_outer` prove the enclosure `{I+At+½(At)² \| A∈A_Z} ⊆ (A_Z.quadTaylor t).construct` by [1]'s own closed-form construction, corrected by the factor of two [1]'s printed `L^(j)` etc. drop (a confirmed erratum, not an extraction artifact; see `## Findings`) — one generator per *unordered* pair `i < j`, carrying `p_i p_j` on the single symmetrized `G^(i)G^(j)+G^(j)G^(i)`, exactly as [1] does, not one independent generator per ordered pair; the `κ+κ+κ²` index type pads the `i ≥ j` half with generators that are always `0`, denoting exactly what [1]'s own `κ+κ+κ(κ-1)/2` does. Minimality — [1]'s own "smallest possible" — is asserted by the source and not formalized here. **Counterexample:** `Zonotope.quadTaylor_printed_counterexample` | `fixed` — printed generators `L^(j)` are off by a factor of two (confirmed erratum) |

## Findings

**`Prop. 3`'s own printed generator formula is off by a factor of two — a confirmed erratum, not
an extraction artifact.** The custom content-stream extractor this page's `Source` line describes
is unreliable for fine numeric detail, so this was first read with `pypdf` (a maintained library,
not this repository's own parser) directly against the same mediaTUM PDF, which renders the whole
proposition and its proof cleanly — subscripts, exponents and all. It confirms the same reading:
`L^(0)(t) = I + G^(0)t + (G^(0)² + Σ 0.5 G^(i)²)t²`, `L^(j)(t) = G^(j)t + (G^(0)G^(j)+G^(j)G^(0))t²`
and `L^(2κ+l)(t) = (G^(j)G^(k)+G^(k)G^(j))t²` — no `0.5` on any of these three, though `L^(0)` and
`L^(κ+j)` do carry one. These do not enclose the stated target `{I+At+½(At)² \| A∈A_Z}` when checked
against the proposition's own expansion of `A²`, which the printed proof derives inline:
substituting `q_j = 2p_j²-1` and `r_{jk}=p_jp_k`, as the proof's own "split `[0,1]` into
`0.5[-1,1]+0.5`" step requires, these coefficients reconstruct `I+At+(At)²` (the full square, no
`½`) rather than the stated `I+At+½(At)²` — every quadratic-derived coefficient is exactly double
what the proposition's own algebra needs, and a correctly-halved version of the same formula does
reconstruct the stated target exactly (this is what `quadTaylor` proves). `quadTaylor` does not
retype `L^(j)` verbatim, uncorrected: the corrected, halved coefficients are what `quadTaylor_outer`
actually needs and proves. The printed generators are written out only in
`Zonotope.quadTaylor_printed_counterexample`, which refutes the enclosure on `A_Z = [0.9, 1.1]`,
`t = 1`: they give `[2.7, 3.31]`, and `A = 0.9` gives `I + A + ½A² = 2.305`.
