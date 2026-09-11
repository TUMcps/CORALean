# Reachability Analysis of Nonlinear Systems using Conservative Polynomialization and Non-Convex Sets

M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
Polynomialization and Non-Convex Sets". HSCC 2013.

**Source:** https://mediatum.ub.tum.de/doc/1283922/39133.pdf (read directly with a custom PDF-content-stream text extractor since no PDF rasterizer was available in this environment — poppler/pdftoppm is not installed, so the Read tool's PDF-page mode is unavailable)  
**Inventory:** confirmed (full 10-page paper read)

Conservative polynomialization: abstracting a nonlinear field to second order
rather than first, so the abstraction error shrinks with the *square* of the
set. `NonlinearSys.deltaReach` and the polynomial abstraction error around it.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Polynomial Zonotope) Given a starting point c, multi-indexed dependent generators f^(i,j,k,...,m) and independent generators g^(i), a polynomial zonotope PZ = {c + Σβ_j f^(β,j) + Σβ_jβ_k f^(β,j,k) + ... + Σγ_i g^(i) \| β_i,γ_i∈[-1,1]} (eq. 13); order ϱ=γ/n; shorthand PZ=(c,E,F,G). | — |
| `Alg. 1` | "reach(R(0),t_f,...)": the paper's overall nonlinear reachability algorithm using polynomial zonotopes, combining Taylor linearization, convex-hull of consecutive steps, Lagrange remainder bounding, and a fixed-point loop over the abstraction error Ω(δ_s). | — |
| `Prop. 1` | (Overapproximation by a Zonotope) A polynomial zonotope PZ=(c,E,F,G) is over-approximated by the zonotope Z=zonotope(PZ)=(c̃,G̃) ⊇ PZ, by making dependent generators independent (halving/folding E₂ into the center and doubling into G); complexity O(n²). | — |
| `Thm. 1` | (Quadratic Map of a Zonotope) Given a zonotope Z=(d,g^(1),...,g^(h)) and matrices Q^(i), the quadratic map sq(Q,Z)={φ \| φ_i=x^T Q^(i) x, x∈Z} is exactly a polynomial zonotope PZ=(c,E,F,G) with explicit formulas for c, E, F (G=∅); complexity O(n⁵). | — |
| `Cor. 1` | (Quadratic Map of a Polynomial Zonotope) Given PZ=(c,E,F,G) and its enclosing zonotope Z=zonotope(PZ) (Prop. 1) split as Z=Z_EF⊕Z_G, the quadratic map is over-approximated by sq(Q,Z) ⊆ sq(Q,Z_EF) ⊕ zonotope(sq(Q,Z_G)); same O(n⁵) complexity as Thm. 1. | — |
| `Prop. 2` | (Overapproximative Generator Removal) Given PZ=(c,E,F,G) and n linearly independent generators picked from E₁ into matrix P, gives a formula for removing one generator g^(i) from G by stretching the picked E₁-generators (via P⁻¹g^(i)) to compensate, yielding an over-approximating PẐ=(c,Ê,F,Ĝ); complexity O(n³) (matrix inversion). | — |

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`PolyAbstractionError.lean`](../src/CORALean/ContDynamics/NonlinearSys/PolyAbstractionError.lean)
