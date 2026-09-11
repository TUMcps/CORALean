# Analyzing Reachability of Linear Dynamic Systems with Parametric Uncertainties

M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic
Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.), Modeling, Design,
and Simulation of Systems with Uncertainties, Springer, 2011.

**Source:** https://mediatum.ub.tum.de/doc/1287218/358815.pdf — this is the authors' own preprint/self-archived copy of the chapter (freely hosted on mediaTUM), NOT the final Springer-typeset book chapter (which is paywalled and was not accessed). Read directly with a custom PDF-content-stream text extractor since no PDF rasterizer was available in this environment (poppler/pdftoppm not installed).  
**Inventory:** confirmed (against the preprint) — but with an UNVERIFIED section-number correspondence to the published book chapter (see notes)

Cited for one construction, the matrix zonotope acting on a zonotope
(`mtimesMatZonotope`). CORA cites the book; the result is in this chapter of it,
which is what the entry now names.

The typeset chapter is paywalled, so the rows below are read off the authors'
own preprint, whose local §4.1 is the book's §4.4.1 — the section our tree used
to cite, now narrowed to the equation inside it. The same construction is Prop. 3.5 of
[Althoff's thesis](2010-althoff-thesis.md).

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Eq. 8` | (Matrix Zonotope) A_Z = {G^(0) + Σ_{i=1}^κ p_i G^(i) \| p_i∈[-1,1], G^(i)∈R^{n×n}}; shorthand A_Z=(G^(0),G^(1),...,G^(κ)); order ϱ=κ/n. | — |
| `Eq. 9` | Matrix zonotopes can equivalently be represented as the convex hull of their matrix vertices V^(i): A_Z = {Σ α_i V^(i) \| α_i∈R, α_i≥0, Σα_i=1}. | — |
| `Eq. 10` | (Matrix Zonotope Product) Gives the multiplication A_Z ⊗ B_Z of two matrix zonotopes A_Z=(G^(0),...,G^(κA)) and B_Z=(H^(0),...,H^(κB)), enclosed by the zonotope (G^(0)H^(0), G^(0)H^(1), ..., G^(κA)H^(κB)) obtained by pairwise-multiplying center/generator matrices — this is the "matrix zonotope product" the CORALean tree cites. | [`MtimesMatZonotope.lean`](../src/CORALean/ContSet/ZonoBundle/Real/Operations/MtimesMatZonotope.lean), [`MtimesMatZonotope.lean`](../src/CORALean/ContSet/Zonotope/Real/Operations/MtimesMatZonotope.lean) |
| `Prop. 3` | (Dependent Matrix Zonotope Evaluation) The set {I + At + 0.5(At)² \| A∈A_Z} (the exact quadratic Taylor term of the matrix exponential for A in a matrix zonotope A_Z) is enclosed by the smallest possible zonotope W_Z(t)=(L^(0)(t),...,L^(κW)(t)), with explicit closed-form generator matrices L^(j)(t) built from products G^(i)G^(j)+G^(j)G^(i) — this exploits the dependency between repeated occurrences of the same matrix generator (rather than treating A_Z⊗A_Z as an independent product) to get a tighter, exact-for-second-order enclosure. | — |
