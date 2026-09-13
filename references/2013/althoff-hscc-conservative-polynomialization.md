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
| `Def. 1` | (Polynomial Zonotope) Given a starting point c, multi-indexed dependent generators f^(i,j,k,...,m) and independent generators g^(i), a polynomial zonotope PZ = {c + Σβ_j f^(β,j) + Σβ_jβ_k f^(β,j,k) + ... + Σγ_i g^(i) \| β_i,γ_i∈[-1,1]} (eq. 13); order ϱ=γ/n; shorthand PZ=(c,E,F,G). | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Alg. 1` | "reach(R(0),t_f,...)": the paper's overall nonlinear reachability algorithm using polynomial zonotopes, combining Taylor linearization, convex-hull of consecutive steps, Lagrange remainder bounding, and a fixed-point loop over the abstraction error Ω(δ_s). | — |
| `Sec. 4.1` | Overapproximating the linearization error: `post∆(R(ts),Ψ(τs),A)` — "a slight modification of the standard techniques for linear system reachability... returning the set of state differences... instead of the set of states" (line 6) — and `lagrangeRemainder(R(τs),E,z*)` (line 8), the boxed third-order Taylor remainder left once the exact second-order (`D`) term is subtracted. | [`PostDelta.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/PostDelta.lean), [`PostDeltaOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/PostDeltaOuter.lean), [`LagrangeRemainder.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/LagrangeRemainder.lean), [`AbstractionErrorOfLagrange.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstractionErrorOfLagrange.lean); `sq`/`mu` (`quadMapDep`, already tracked as `Thm. 1`/`Cor. 1` above) and the `enlarge`/repeat-until loop (lines 4-10) are not covered — CORALean's abstraction-error apparatus is a certificate design (`AbstrErrPolySearch`) that searches caller-supplied candidates rather than iterating a fixed point; `Sec. 4.2`'s `varInputs`, the same `mu` applied to an *independent* pair of ranges rather than a shared factor vector, is not yet built |
| `Prop. 1` | (Overapproximation by a Zonotope) A polynomial zonotope PZ=(c,E,F,G) is over-approximated by the zonotope Z=zonotope(PZ)=(c̃,G̃) ⊇ PZ, by making dependent generators independent (halving/folding E₂ into the center and doubling into G); complexity O(n²). | [`PolyZonotope_to_Zonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Zonotope.lean) — `PolyZonotope.zonotopeEven`/`zonotopeEven_contains` is the halving-into-centre reading Prop. 1 states exactly; the plain `zonotope` alongside it is the cruder, non-halving reading `[1, Prop. 2.6]` uses. |
| `Thm. 1` | (Quadratic Map of a Zonotope) Given a zonotope Z=(d,g^(1),...,g^(h)) and matrices Q^(i), the quadratic map sq(Q,Z)={φ \| φ_i=x^T Q^(i) x, x∈Z} is exactly a polynomial zonotope PZ=(c,E,F,G) with explicit formulas for c, E, F (G=∅); complexity O(n⁵). | [`Zonotope_to_PolyZonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/Zonotope_to_PolyZonotope.lean), [`QuadMapExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/QuadMapExact.lean) — `Zonotope.polyZonotope_exact` (a zonotope *is* a polynomial zonotope, exactly) composed with `PolyZonotope.quadMap_exact` (`quadMap` is exactly the quadratic-map image, at any polynomial zonotope) gives exactly this: a zonotope's quadratic-map image equals a polynomial zonotope's `construct`. |
| `Cor. 1` | (Quadratic Map of a Polynomial Zonotope) Given PZ=(c,E,F,G) and its enclosing zonotope Z=zonotope(PZ) (Prop. 1) split as Z=Z_EF⊕Z_G, the quadratic map is over-approximated by sq(Q,Z) ⊆ sq(Q,Z_EF) ⊕ zonotope(sq(Q,Z_G)); same O(n⁵) complexity as Thm. 1. | n/a — restated; tracked as `Prop. 13` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Prop. 2` | (Overapproximative Generator Removal) Given PZ=(c,E,F,G) and n linearly independent generators picked from E₁ into matrix P, gives a formula for removing one generator g^(i) from G by stretching the picked E₁-generators (via P⁻¹g^(i)) to compensate, yielding an over-approximating PẐ=(c,Ê,F,Ĝ); complexity O(n³) (matrix inversion). | — |

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`PolyAbstractionError.lean`](../../src/CORALean/ContDynamics/NonlinearSys/PolyAbstractionError.lean)
