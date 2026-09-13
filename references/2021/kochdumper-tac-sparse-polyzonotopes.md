# Sparse Polynomial Zonotopes: A Novel Set Representation for Reachability Analysis

N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set Representation
for Reachability Analysis". IEEE Transactions on Automatic Control, 2021.

**Source:** https://arxiv.org/pdf/1901.01780 (read as the PDF, whose numbering agrees with the ar5iv rendering at https://ar5iv.labs.arxiv.org/html/1901.01780 this page was first read from)  
**Inventory:** confirmed

The polynomial zonotope: generators carrying monomials in the factors, so a
set stays non-convex and a quadratic map stays exact. `PolyZonotope` and most
of what it can do.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Sparse Polynomial Zonotope) PZ = { Σ_i (Π_k α_k^E(k,i)) G_(·,i) + Σ_j β_j G_I(·,j) \| α_k,β_j∈[-1,1] }, given dependent-generator matrix G, independent-generator matrix G_I, exponent matrix E. | [`PolyZonotope.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/PolyZonotope.lean) |
| `Prop. 1` | (Merge ID) mergeID returns two adjusted SPZs (from two SPZs with different identifier vectors) with identical identifier vectors, equivalent to the originals, with complexity O(n²). | [`PadBackExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/PadBackExact.lean) |
| `Prop. 2` | (Compact) compact(PZ) returns a compressed SPZ representation (merging generators with identical exponent columns) with complexity O(n²log(n)). | [`CompactExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/CompactExact.lean) |
| `Def. 2` | (Zonotope) [cites [31, Def. 1]] Z = {c + Σ α_i G_(·,i) \| α_i∈[-1,1]}, shorthand Z=⟨c,G⟩_Z; any zonotope can be converted to an SPZ. | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Prop. 3` | (Conversion Zonotope) A zonotope Z=⟨c,G⟩_Z can be represented as the SPZ ⟨[c G],[ ],[0 I_l],uniqueID(l)⟩_PZ, with conversion complexity O(l). | [`Zonotope_to_PolyZonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/Zonotope_to_PolyZonotope.lean) |
| `Def. 3` | (Polytope) [cites [4, Def. 2.2]] Vertex representation P = {Σ λ_i v_i \| λ_i≥0, Σλ_i=1}, shorthand ⟨[v_1...v_r]⟩_P. | n/a — restated from an earlier paper, which this formalization does not draw on directly |
| `Thm. 1` | (Conversion Polytope) Every bounded polytope can be equivalently represented as an SPZ (via convex hull of vertex-SPZs, using that SPZs without independent generators are closed under convex hull per Prop. 14). | [`VPolytope_to_PolyZonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/VPolytope_to_PolyZonotope.lean) |
| `Def. 4` | (Taylor Model) [cites [21, Def. 2.1]] Standard Taylor-model definition over a polynomial vector field w and remainder interval I. | n/a — restated from an earlier paper, which this formalization does not draw on directly |
| `Prop. 4` | (Conversion Taylor Model) A Taylor model T(x)=⟨w(x),I⟩_T on a domain D can be equivalently represented by an SPZ. | n/a — Taylor models are a subject CORALean does not cover: there is no `TaylorModel` set representation under `ContSet/` and none is intended for now, so a conversion into one has no source to convert from. CORA has `@taylm`; if that changes, this row comes back into scope |
| `Prop. 5` | (Zonotope) zono(PZ) returns an enclosing zonotope for an SPZ PZ=⟨G,G_I,E,id⟩_PZ with complexity O(n²), by classifying generators into center-contributing (N), even-exponent (H), and remaining (K) sets. | [`PolyZonotope_to_Zonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Zonotope.lean) |
| `Prop. 6` | (Polytope) poly(PZ) returns an enclosing polytope for an SPZ, computed via vertex enumeration of a related SPZ (using [40, Alg. 2]), complexity O(2^{n²}). | [`PolyZonotope_to_VPolytope.lean`](../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_VPolytope.lean) |
| `Def. 5` | (Support Function) [cites [32, Def. 1]] s_S(d) = max_{x∈S} d^T x; exact for convex sets, an over-approximation for non-convex sets such as SPZs. | n/a — restated from an earlier paper, which this formalization does not draw on directly |
| `Prop. 7` | (Support Function) An SPZ is over-approximated by the support function ŝ_PZ(d) = u + Σ\|ḡ_I(j)\|, computed via a Bernstein-type bound B(w(α),[-1,1]) on the dependent-generator polynomial. | [`SupportBound.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/SupportBound.lean) |
| `Prop. 8` | (Multiplication) M⊗PZ = ⟨MG,MG_I,E,id⟩_PZ for left-multiplication of an SPZ by matrix M, complexity O(mn²). | [`MulExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MulExact.lean) |
| `Prop. 9` | (Addition) Minkowski sum PZ1 ⊕ PZ2 (with a zonotope Z) via concatenation of generator/exponent matrices with block-diagonal padding and uniqueID for the merged identifier vector. | [`PlusExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/PlusExact.lean) |
| `Prop. 10` | (Exact Addition) For two SPZs sharing a common identifier vector id, their "exact addition" PZ1 ⊞ PZ2 = ⟨[G1 G2],[GI1 GI2],[E1 E2],id⟩_PZ (no padding needed, exact — not an over-approximating Minkowski sum). | [`ExactPlusPoint.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ExactPlusPoint.lean) |
| `Prop. 11` | (Cartesian Product) Formula for PZ1 × PZ2 (with a zonotope Z) via block-diagonal concatenation of generator and exponent matrices. | [`CartProdExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/CartProdExact.lean) |
| `Def. 6` | (Quadratic Map) [cites [5, Theorem 1]] sq(Q,S) = {x \| x_(i) = s^T Q_i s, s∈S, i=1..m} for a discrete set of matrices Q_i. | n/a — restated from an earlier paper, which this formalization does not draw on directly |
| `Prop. 12` | Gives the exact quadratic map sq(Q,PẐ) for an SPZ PẐ without independent generators, as an SPZ with exponent/generator matrices built from pairwise products of the original ones. | [`QuadMapDepExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/QuadMapDepExact.lean) |
| `Prop. 13` | (Quadratic Map) Over-approximates sq(Q,PZ) for a general SPZ (with independent generators) by combining the exact quadratic-map construction of Prop. 12 with a zono() enclosure (Prop. 5) for cross terms. | [`QuadMapExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/QuadMapExact.lean) |
| `Def. 7` | (Convex Hull) conv(S1,S2) = {0.5(1+λ)s1 + 0.5(1-λ)s2 \| s1∈S1, s2∈S2, λ∈[-1,1]}. | [`ContSet.lean`](../../src/CORALean/ContSet/ContSet/ContSet.lean) |
| `Prop. 14` | Gives the exact convex hull conv(PZ1,PZ2) for two SPZs without independent generators, as an SPZ built by doubling and negating generator/exponent blocks with a new identifier. | [`LinCombExactOfDependent.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/LinCombExactOfDependent.lean) |
| `Prop. 15` | (Convex Hull) Over-approximates conv(PZ1,PZ2) for general SPZs (with independent generators) by combining Prop. 14 on the dependent parts with a zonotope convex-hull enclosure for the independent parts. | [`LinCombOuter.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/LinCombOuter.lean) |
| `Prop. 16` | (Reduce) reduce(PZ,ρ_d) returns an SPZ of order ≤ ρ_d enclosing PZ, by moving a subset of dependent/independent generators into a zonotope over-approximation via zono() and reduce() on that zonotope. | [`ReduceOuter.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ReduceOuter.lean) |
| `Prop. 17` | (Restructure) restructure(PZ) returns an SPZ enclosing PZ with all independent generators removed, by reducing the independent-generator zonotope part to order 1 and re-expressing it with new dependent generators/exponents. | [`RestructureOuter.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/RestructureOuter.lean) |
| `Def. 8` | (Reachable Set) R^e_{X0}(t) := {ξ(t,x0,u(·)) \| x0∈X0, ∀τ∈[0,t] u(τ)∈U}, the standard reachable-set definition for the nonlinear system under study. | [`ReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/ReachSet.lean) |
| `Alg. 1` | "Compute a tight enclosure of the reachable set": the paper's overall nonlinear reachability algorithm using SPZs (Taylor expansion at a linearization point z*, propagation, and set operations from the Propositions above). | [`AbstrErrPolySearch.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrErrPolySearch.lean), [`RelinReach.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/RelinReach.lean), [`RelinTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/RelinTimeInterval.lean), [`ReachSetSubsetRelinTimeIntervalHorizon.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachSetSubsetRelinTimeIntervalHorizon.lean), [`Polynomialization.lean`](../../src/CORALean/Examples/Polynomialization.lean); lines 19-21, the `volRatio` test and `restructure`, are not called from the loop, and line 17's `post` adds with `Prop. 9`'s Minkowski sum rather than `Prop. 10`'s exact addition — both cost tightness, not soundness |

## Findings

**Prop. 3, Prop. 6, Prop. 7, and Eq. (11) of Prop. 9.** A zero exponent column and the
factor box are written with `n` rows — `0^{(n,1)}`, and `[-1^{(n,1)}, 1^{(n,1)}]` — where
the number of *factors* is meant: `l` in Prop. 3, `p` in Prop. 6 and Prop. 7, `p₁` in
Eq. (11). Prop. 4 writes the same column correctly, at `0^{(s,1)}`. Every construction is
right as intended, and CORA is unaffected.

**Prop. 5.** Its proof calls a monomial with exclusively even exponents "strictly
positive". It is non-negative — `α_k = 0` at a positive exponent gives `0` — and the
proof's own next line writes the range as `[0,1]`, which is what the enclosure uses. The
result is right either way. [`PolyZonotope_to_Zonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Zonotope.lean)

**Prop. 6.** The SPZ it builds, `PZ̄`, carries an independent block `[G_I G_z]`, but the
vertex enumeration it is handed to — [40, Alg. 2] — takes a representation with none. The
independent generators have to be read as dependent ones at fresh factors of exponent one,
which is the paper's own Prop. 3, and the statement does not say so. `Ḡ_(·,K)` and
`Ē_(·,K)` in Eq. (9) carry overlines that are never defined; the proof writes both blocks
plain. The sentence after the proof credits Fig. 3 (middle) to "Prop. 9", the Minkowski
sum, where `(9)` is the equation and Prop. 6 the result. Soundness for a *non-convex*
zero-one SPZ, which is the case Prop. 6 needs, is asserted in [40] in the prose under
Alg. 2 rather than in a numbered result — [40, Prop. 5] is about where a polytope's
vertices sit. Everything is right as intended.
[`PolyZonotope_to_VPolytope.lean`](../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_VPolytope.lean)

**Alg. 1.** Its parameters do not match its text. `enlarge` is defined to take "a
scalar factor λ ∈ ℝ_{>1}", and every value the paper gives for λ — the default and all
three benchmarks — is `0.1`; read as the fractional increment CORA applies, a factor of
`1.1`, the algorithm and the numbers agree and only the stated domain is wrong. And
`Require:` lists `ρ_d` and `µ_d` but not `p_d`, the bound on the number of factors after
restructuring that Sec. II-E.2 introduces and that every benchmark reports, so line 20's
`restructure(R(t_{s+1}))` is written without the argument that limits it. Neither affects
soundness.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`API.lean`](../../src/CORALean/ContSet/PolyZonotope/API.lean)
