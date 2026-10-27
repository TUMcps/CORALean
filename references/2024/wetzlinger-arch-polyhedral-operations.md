# Implementation of Polyhedral Operations in CORA 2024

```bibtex
@inproceedings{wetzlinger2024implementation,
  author = {Wetzlinger, M. and Kotsev, V. and Kulmburg, A. and Althoff, M.},
  title = {Implementation of Polyhedral Operations in CORA 2024},
  booktitle = {Proceedings of the 11th Int. Workshop on Applied Verification for Continuous and Hybrid Systems},
  year = {2024}
}
```

**In the paper's bibliography.**

**Source:** https://easychair.org/publications/paper/81TW (the EPiC PDF, 19 pages, pp. 163-181, read in full; text extracted with `pypdf`, Table 1 again with its layout kept. The TUM repository copy <https://mediatum.ub.tum.de/doc/1763183/1763183.pdf> is the same file.)  
**Inventory:** confirmed (the numbered items are Definitions 1-3, Algorithms 1-3, equations (1)-(37), Tables 1-4, Figure 1 and footnotes 1-3; footnotes 1 and 2 are a link and a side condition of the cited Quickhull analysis, footnote 3 a claim. The claims stated in prose without a number are rows of their own, named by section)

The tool paper of CORA's `@polytope` class, cited by ten of its methods: for each operation the
paper gives the formula or linear program CORA evaluates, for the halfspace and the vertex
representation, and its running time. The support function is the paper's workhorse, and the tree
states it once, in `[-∞, +∞]` (`supportFunc`), so that the paper's conventions for empty and
unbounded sets are the definition rather than cases. Table 1, how the binary operations act on
the properties CORA caches, is formalized for arbitrary sets. Several statements fail at the empty
set, which the paper itself makes degenerate and bounded; three more are misprinted (the
degeneracy test of `Eq. 18`, line 4 of `Alg. 1`, the dimensions in `Eq. 24`), and two are false
outright (a speed-up for redundancy removal, and the basis of `Eq. 20` without column pivoting).
The running times are one row, a cost the tree asserts and cannot prove.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (H-polyhedra and H-polytopes, [1, Sec. 1.1]) `P = ⟨A, b⟩_H = {x ∈ ℝⁿ \| Ax ≤ b}`, a polytope if bounded; no constraints means `ℝⁿ`. | n/a — the textbook halfspace representation, restated from Ziegler's *Lectures on Polytopes*, which has no page here; `HPolytope.ineqs` is the tree's form | `restated` |
| `Def. 2` | (V-polytopes, [1, Sec. 1.1]) `⟨[v₁ … vₘ]⟩_V` is the set of convex combinations of the points; non-redundant points are vertices; no points gives `∅`. | n/a — restated from Ziegler, as `Def. 1`; `VPolytope.construct` is the tree's form, empty for `k = 0` | `restated` |
| `Def. 3` | (Degenerate and non-degenerate sets) `S` is non-degenerate if its interior is nonempty; equivalently, `S` is degenerate iff `∀ s ∈ S, ∀ ε > 0: s ⊕ B_ε ⊄ S`; `∅` is degenerate. | [`InteriorEqEmptyIffForallBall.lean`](../../src/CORALean/ContSet/ContSet/Theorems/InteriorEqEmptyIffForallBall.lean) — the equivalence, with `B_ε` the Euclidean ball read through `toEuclidean` | `correct` |
| `Sec. 3` | Empty sets are bounded and degenerate; non-degenerate sets and unbounded sets are nonempty; properties combine pairwise, e.g. a nonempty set times a degenerate, unbounded one is degenerate and unbounded. | [`PropertyFacts.lean`](../../src/CORALean/ContSet/ContSet/Theorems/PropertyFacts.lean) — the set properties | `correct` |
| `Sec. 3 (minimal representation)` | Empty sets are in minimal representation. | [`KEqZeroOfConstructEqEmpty.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/KEqZeroOfConstructEqEmpty.lean), [`EmptySetRowsMinimal.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/EmptySetRowsMinimal.lean), [`EmptyRedundant.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/EmptyRedundant.lean) — a V-representation of `∅` lists no points (`VPolytope.k_eq_zero_of_construct_eq_empty`), and CORA's one-row H-representation `0 ≤ -1` has the fewest rows any H-representation of `∅` has (`HPolytope.emptySet_rows_minimal`); an H-representation of `∅` can still carry a redundant row, `x ≤ -1, -x ≤ -1, x ≤ 5` (`HPolytope.empty_redundant_counterexample`) | `underspecified` — minimal representation is a property of a representation, not of a set; it holds of every V-representation of `∅` and of the one-row H-representation, not of every H-representation of `∅`; see Findings |
| `Table 1 (MS)` | An invertible `M` keeps emptiness, non-emptiness, (non-)degeneracy and (un)boundedness of `S`; a singular `M` maps `E → E`, `NE → NE, D`, `D → D`, `ND → NE, D`, `B → B`, `NB → –`. | [`ImageLinearMapProperties.lean`](../../src/CORALean/ContSet/ContSet/Theorems/ImageLinearMapProperties.lean) — every cell, for any set `S ⊆ ℝⁿ` | `correct` |
| `Table 1 (⊕)` | Effect of `S₁ ⊕ S₂` on the six properties, e.g. `E ⊕ · = E`, `NE ⊕ ND = ND`, `NE ⊕ NB = NB`, `B ⊕ B = B`, and `D ⊕ ND = ND`, `D ⊕ NB = NB`, `ND ⊕ B = ND`, `B ⊕ NB = NB`. | [`AddProperties.lean`](../../src/CORALean/ContSet/ContSet/Theorems/AddProperties.lean), [`AddProperties.lean`](../../src/CORALean/ContSet/ContSet/Counterexamples/AddProperties.lean) — the cells that hold, and the four last ones with a nonempty first summand; the counterexample `∅ ⊕ ℝⁿ = ∅` | `underspecified` — four cells fail only at `∅`, degenerate and bounded by the paper's own convention; the first summand nonempty is supplied; see Findings |
| `Table 1 (⊖)` | Effect of `S₁ ⊖ S₂`, e.g. `· ⊖ E = ND, NB`, `D ⊖ ND = E`, `B ⊖ NE = B`, `B ⊖ NB = E`, and `E ⊖ D = E`, `E ⊖ B = E`, `B ⊖ D = B`, `B ⊖ B = B`. | [`MinkowskiDiffProperties.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffProperties.lean), [`MinkowskiDiffProperties.lean`](../../src/CORALean/ContSet/ContSet/Counterexamples/MinkowskiDiffProperties.lean) — `minkowskiDiff` is [1, Table 3]'s `⊖`; the cells that hold, the four last ones with a nonempty subtrahend, and `∅ ⊖ ∅ = ℝⁿ` | `underspecified` — four cells fail only at a subtrahend `∅`, which the paper's convention excludes; it nonempty is supplied; see Findings |
| `Table 1 (×)` | Effect of `S₁ × S₂`, e.g. `NE × D = D`, `NE × NB = NB`, `D × ND = D`, `B × B = B`, and `D × B = D, B`, `D × NB = D, NB`. | [`ProdProperties.lean`](../../src/CORALean/ContSet/ContSet/Theorems/ProdProperties.lean), [`ProdProperties.lean`](../../src/CORALean/ContSet/ContSet/Counterexamples/ProdProperties.lean) — on the product type, a linear homeomorphism away from the stacked `ℝ^{n₁+n₂}`; the counterexamples a line times a point and `∅ × ℝ` | `underspecified` — `D × B` is not bounded in general and `D × NB` not unbounded only at `∅`; a degenerate factor gives a degenerate product, and nonempty factors are supplied; see Findings |
| `Table 1 (conv)` | Effect of `conv(S₁, S₂)`, e.g. `conv(E, ·) = E`, `conv(NE, ND) = ND, NE`, `conv(B, B) = B`, and `conv(D, ND) = ND`, `conv(D, NB) = NB`, `conv(ND, B) = ND`, `conv(B, NB) = NB`. | [`SetLinCombProperties.lean`](../../src/CORALean/ContSet/ContSet/Theorems/SetLinCombProperties.lean), [`SetLinCombProperties.lean`](../../src/CORALean/ContSet/ContSet/Counterexamples/SetLinCombProperties.lean) — `Set.linComb` is [1, Table 3]'s `conv`; the counterexample `conv(∅, ℝⁿ) = ∅` | `underspecified` — four cells fail only at `∅`, which the paper's convention excludes; both operands nonempty is supplied; see Findings |
| `Table 1 (∩)` | Effect of `S₁ ∩ S₂`: with `E` it is `E`, with `D` it is `D`, with `B` it is `B`; nothing else is claimed. | [`InterProperties.lean`](../../src/CORALean/ContSet/ContSet/Theorems/InterProperties.lean) | `correct` |
| `Eq. 1` | The `j`-th halfspace of `⟨A, b⟩_H` is redundant iff `ρ(⟨A, b⟩_H, A(j,·)ᵀ) = ρ(⟨A*, b*⟩_H, A(j,·)ᵀ)`, `⟨A*, b*⟩` without row `j`; this works whether the polyhedron is bounded or degenerate. | [`IneqsEqDropIffSupportFunc.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsEqDropIffSupportFunc.lean) — `supportFunc` in `[-∞, +∞]`, as `Eq. 33` fixes it | `correct` |
| `Sec. 4.1 (support vector)` | If the `j`-th halfspace is redundant, the support vector `ν` of `⟨A*, b*⟩_H` along its normal is a vertex of `⟨A, b⟩_H`, and every halfspace `k ≠ j` with `A(k,·) ν = b(k)` is non-redundant. | [`TightRedundant.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/TightRedundant.lean) — the unit square with `x + y ≤ 2` and `x + y ≤ 3`: the latter is redundant, `(1, 1)` its support vector, and `x + y ≤ 2` is tight there and redundant | `false` — a halfspace tight at a vertex need not define a facet; no restriction of the claim is stated to repair it; see Findings |
| `Sec. 4.1 (interval hull)` | All halfspaces that strictly contain the interval hull of the polytope can be removed. | [`IneqsEqOfStrict.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsEqOfStrict.lean), [`IneqsEqOfStrict.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IneqsEqOfStrict.lean) — for a nonempty polytope and any enclosure `T` in place of the interval hull; the counterexample `{x ≤ 0, -x ≤ -1}` | `underspecified` — fails only at an empty polytope, whose interval hull is empty, which the paper's setting excludes; a nonempty one is supplied; see Findings |
| `Eq. 2` | The `j`-th point is redundant iff it lies in the V-polytope of the others. | [`ConstructEqDropIff.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/ConstructEqDropIff.lean) | `correct` |
| `Sec. 4.1 (V affine hull)` | With `B = U Σ Vᵀ` a basis of the affine hull of `P = ⟨[v₁ … vₘ]⟩_V` and `c ∈ P`, `M = [I_r 0] Uᵀ`, the polytope `P' = ⟨[M(v₁ - c) … M(vₘ - c)]⟩_V` is non-degenerate and `P = Mᵀ P' + c`. | [`RestrictAffineHull.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/RestrictAffineHull.lean) — `U` orthogonal with its first `r` columns spanning the direction of the hull (what the decomposition gives) and `c` in the hull are hypotheses | `correct` |
| `Sec. 4.1 (H vertex enumeration)` | With `B` a basis of the affine hull of `P = ⟨A, b⟩_H` and `c ∈ P`, `P' = ⟨A B, b - A c⟩_H` is non-degenerate and `P = B P' + c`. | [`IneqsEqImageRestrict.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsEqImageRestrict.lean), [`InteriorRestrictNonempty.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/InteriorRestrictNonempty.lean) — the equality needs only `P ⊆ c + span(B)`; non-degeneracy needs `B` injective with range the direction of the hull | `correct` |
| `Sec. 4.1 (conversions)` | Facet enumeration by Quickhull, the facets turned into halfspaces by Gram–Schmidt; vertex enumeration by the primal-dual method [21], [1, Ch. 2.3]; an error for unbounded polyhedra. | n/a — restated from Bremner, Fukuda and Marzetta and from Ziegler, neither with a page here; the tree's conversions are `HPolytope.vPolytope` and `VPolytope.hPolytope` | `restated` |
| `Eq. 3` | `⟨V₁⟩_V ⊆ ⟨V₂⟩_V` iff every point of `V₁` lies in `⟨V₂⟩_V`. | [`SubsetIffVertexMem.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SubsetIffVertexMem.lean) | `correct` |
| `Eq. 4` | Point containment in a V-polytope is the feasibility of the linear program `v = [v₁ … vₘ] β`, `∑ β = 1`, `β ≥ 0`. | n/a — the program is `VPolytope.construct` written out; nothing to prove beyond `Eq. 3` | `not-a-claim` |
| `Sec. 4 (hardness)` | H-polyhedron in V-polytope containment is NP-hard [22]; the Minkowski sum of two H-polytopes and the intersection of two V-polytopes are NP-hard [24]. | n/a — restated from Kellner, Theobald and Trabandt and from Tiwary, neither with a page here | `restated` |
| `Sec. 4.2 (unbounded)` | An H-polyhedron known to be unbounded is in no V-polytope. | [`NotSubsetOfNotIsBounded.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/NotSubsetOfNotIsBounded.lean) | `correct` |
| `Eq. 5` | `⟨A₁, b₁⟩_H ⊆ ⟨A₂, b₂⟩_H` iff `ρ(⟨A₁, b₁⟩_H, A₂(j,·)) ≤ b₂(j)` for every `j`. | [`IneqsSubsetIffSupportFunc.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsSubsetIffSupportFunc.lean) | `correct` |
| `Eq. 6` | `⟨[v₁ … vₘ]⟩_V ⊆ ⟨A, b⟩_H` iff `A vⱼ ≤ b` for every `j`. | [`SubsetIneqsIff.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SubsetIneqsIff.lean) | `correct` |
| `Eq. 7` | `⟨V₁⟩_V = ⟨V₂⟩_V` iff every point of each list is a point of the other or redundant in its own list (in the sense of `Eq. 2`). | [`ConstructEqIffOfInjective.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/ConstructEqIffOfInjective.lean), [`ConstructEqIff.lean`](../../src/CORALean/ContSet/VPolytope/Real/Counterexamples/ConstructEqIff.lean) — for lists without repeated points; the counterexample `⟨[0 0]⟩` against `⟨[1 1]⟩` **Counterexample:** `VPolytope.construct_eq_iff_counterexample` | `fixed` — false when a list repeats a point, which is then redundant by its copy; true for distinct points; see Findings |
| `Alg. 1` | Set equality of two non-degenerate H-polytopes in minimal representation: normalize the rows. Return `⊥` if a row of one has no equal row in the other and `ρ(⟨A₁*, b₁*⟩_H, A₁(j,·)ᵀ) = b₁(j)` (line 4); the same with indices switched; else `⊤`. | [`IsequalNondeg.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/IsequalNondeg.lean), [`IsequalNondegIff.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsequalNondegIff.lean), [`IsequalNondegPrinted.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IsequalNondegPrinted.lean), [`IsequalNondegDuplicate.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IsequalNondegDuplicate.lean) — line 4 read as the text describes it (the row fails unless redundant). Decides equality for non-degenerate minimal input without zero rows; as printed it accepts `[0, 1] = [0, 2]`; without minimality, a repeated row passes | `underspecified` — line 4 prints the failure condition as `ρ = b₁(j)`, which no row of a minimal representation meets; see Findings |
| `Eq. 8` | For degenerate H-polytopes, equality by mutual containment, each by `Eq. 5`. | [`IneqsEqIffSupportFunc.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsEqIffSupportFunc.lean) | `correct` |
| `Eq. 9` | `⟨A, b⟩_H` is empty iff the linear program (10) is feasible with `y* < 0`. | [`IneqsEqEmptyIff.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsEqEmptyIff.lean) — `∃ y ≥ 0, Aᵀ y = 0, bᵀ y < 0`, by Farkas' lemma | `underspecified` — the optimum of (10) over a cone is `0` or `-∞`, never a negative number; read as "some feasible `y` has `bᵀ y < 0`" |
| `Eq. 10` | `y* = min bᵀ y` s.t. `Aᵀ y = 0`, `y ≥ 0`. | n/a — the program `Eq. 9` tests | `not-a-claim` |
| `Eq. 11` | Two V-polytopes intersect iff the linear program (12) is feasible. | [`InterNonemptyIff.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/InterNonemptyIff.lean) | `correct` |
| `Eq. 12` | The program: `[v⁽¹⁾] β₁ = [v⁽²⁾] β₂` with both `β` convex weights. | n/a — the program `Eq. 11` tests | `not-a-claim` |
| `Eq. 13` | Two H-polytopes intersect iff their stacked system (36) is not empty, one emptiness check (9). | [`IneqsInterNonemptyIff.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsInterNonemptyIff.lean) | `correct` |
| `Eq. 14` | A V-polytope and an H-polytope intersect iff the linear program (15) is feasible. | [`InterIneqsNonemptyIff.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/InterIneqsNonemptyIff.lean) | `correct` |
| `Eq. 15` | The program: `A x ≤ b`, `[v₁ … vₘ] β = x` with `β` convex weights. | n/a — the program `Eq. 14` tests | `not-a-claim` |
| `Eq. 16` | An H-polyhedron is bounded iff its support function is bounded along the `n + 1` normals of a simplex, the rows of `[Iₙ -1]ᵀ`. | [`IsBoundedIffSimplexSupportFunc.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsBoundedIffSimplexSupportFunc.lean) — for any `HPolytope`, equality rows included | `correct` |
| `Sec. 4.2 fn. 3` | A simplex has `n + 1` halfspaces, the smallest number for any bounded, non-degenerate H-polytope; dually, a non-degenerate V-polytope needs at least `n + 1` points. | [`SuccLeOfIsBounded.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/SuccLeOfIsBounded.lean), [`SuccLeOfInteriorNonempty.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SuccLeOfInteriorNonempty.lean) — nonemptiness suffices for the halfspace count; `n ≥ 1`, the paper's `ℝⁿ` | `correct` |
| `Eq. 17` | A V-polytope is degenerate iff `rank([v₁ - v̄ … vₘ - v̄]) < n`, `v̄` the mean of the points. | [`InteriorEqEmptyIffRankLt.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/InteriorEqEmptyIffRankLt.lean) — at least one point, for the mean | `correct` |
| `Eq. 18` | `degenerate(⟨A, b⟩_H) ← ⊤ if r > 0`, `r` the optimum of (19); the text adds: radius `0` means degenerate. | [`InteriorNonemptyIffChebyshev.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/InteriorNonemptyIffChebyshev.lean), [`IneqsDegenerateChebyshev.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IneqsDegenerateChebyshev.lean) — non-degenerate iff some `r > 0` is feasible in (19); the counterexample `[0, 1]`, radius `1/2`, non-degenerate **Counterexample:** `HPolytope.ineqs_degenerate_chebyshev_counterexample` | `fixed` — the display has the test reversed; the text beside it is right; see Findings |
| `Eq. 19` | (Chebyshev center, [2, Sec. 8.5.1]) `max r` s.t. `A(j,·) c + r ‖A(j,·)‖₂ ≤ b(j)`, `r ≥ 0`; infeasible means empty. | n/a — restated from Boyd and Vandenberghe's *Convex Optimization*, which has no page here; the ball-in-halfspace condition is proved in `InteriorNonemptyIffChebyshev.lean` for `Eq. 18` | `restated` |
| `Sec. 4.3 (Chebyshev)` | The Chebyshev center is not necessarily unique, e.g. for a rectangle. | [`ChebyshevNotUnique.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ChebyshevNotUnique.lean) — `[0, 2] × [0, 1]`, radius `1/2` at two centers | `correct` |
| `Table 2` | Definitions of containment, set equality, emptiness, intersection, boundedness and degeneracy. | n/a — textbook definitions; the tree states them as `⊆`, `=`, `= ∅`, `Set.Nonempty`, `Bornology.IsBounded` and `interior · = ∅` | `restated` |
| `Table 3` | Definitions of the set operations: linear map, Minkowski sum and difference, Cartesian product, `conv(S₁, S₂) = {λ s₁ + (1 - λ) s₂}`, support function and vector, intersection, union. | n/a — definitions; `minkowskiDiff`, `Set.linComb` and `supportFunc` are the tree's | `restated` |
| `Eq. 20` | The basis of the affine hull of a V-polytope: `B = [Q(·,1) … Q(·,r)]` with `QR = V̄`, `r = rank V̄`, `V̄ = [v₁ - v̄ … vₘ - v̄]`. | [`SpanQrColsEqOfIndep.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SpanQrColsEqOfIndep.lean), [`SpanQrCols.lean`](../../src/CORALean/ContSet/VPolytope/Real/Counterexamples/SpanQrCols.lean) — when the first `r` columns of `V̄` are independent (column pivoting); the counterexample `±e₁, ±e₃` with `Q = I` **Counterexample:** `VPolytope.span_qr_cols_counterexample` | `fixed` — without pivoting the first `r` columns of `Q` need not span the column space; see Findings |
| `Alg. 2` | Basis of the affine hull of an H-polytope: shift by the Chebyshev center, then append the maximizer `x_iter` of (22), perpendicular to the columns so far, until `‖x_iter‖∞ ≤ ε`; `x_iter = 0` implies `P_shift ⊆ span(B)`, and `B` is an orthonormal basis. | [`AffineHullBasis.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/AffineHullBasis.lean), [`AffineHullBasisSpec.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AffineHullBasisSpec.lean) — the maximizer an argument with its specification, the cap `φ` included; columns orthogonal, nonzero, in the span of `P - c`, and `P - c` within `ε` of their span | `underspecified` — line 8 appends `x_iter` unscaled, so `B` is orthogonal, not orthonormal; the maximizer is not specified beyond (22); see Findings |
| `Eq. 21` | `max ‖x‖∞` over `x + B w ∈ P_shift`, `x ⊥ B`. | n/a — the program `Alg. 2` solves; its use is `AffineHullBasisSpec.lean` | `not-a-claim` |
| `Eq. 22` | (21) is equivalent to the maximum over `y ∈ {±e₁, …, ±eₙ}` of the linear objective `yᵀ x`, `2n` linear programs. | [`IsGreatestSignedUnit.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsGreatestSignedUnit.lean) — `‖x‖∞` is the largest `±eᵢᵀ x`, `n ≥ 1` | `correct` |
| `Eq. 23` | `M ⟨[v₁ … vₘ]⟩_V = ⟨[M v₁ … M vₘ]⟩_V`. | [`Mtimes.lean`](../../src/CORALean/ContSet/VPolytope/Real/Operations/Mtimes.lean), [`MtimesExact.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/MtimesExact.lean) | `correct` |
| `Eq. 24` | `M ⟨A, b⟩_H = ⟨A M⁻¹, b⟩_H` for invertible `M`; otherwise `U [I_r 0] ⟨A V [D⁻¹ 0; 0 Iₙ], b⟩_H` with `M = U Σ Vᵀ`, `Σ = [D 0; 0 0]`, `D ∈ ℝ^{(m-r)×n}`, the projection done by Fourier–Motzkin. | [`ImageIneqsOfInvertible.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ImageIneqsOfInvertible.lean), [`ImageIneqsOfFactor.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ImageIneqsOfFactor.lean) — the invertible case; the general one for any `M = U E S Vᵀ`, `V` orthogonal, `S` invertible, the projection left as an image | `underspecified` — the dimensions are misprinted (`D` is `r × r`, the identity block `I_{n-r}`, and `U [I_r 0]` is `m × n` only with zero rows below); see Findings |
| `Eq. 25` | `⟨V₁⟩_V ⊕ ⟨V₂⟩_V` is the V-polytope of all pairwise sums of points. | [`Plus.lean`](../../src/CORALean/ContSet/VPolytope/Real/Operations/Plus.lean), [`PlusExact.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/PlusExact.lean) | `correct` |
| `Eq. 26` | `⟨A₁, b₁⟩_H ⊕ ⟨A₂, b₂⟩_H = [Iₙ Iₙ] ⟨blkdiag(A₁, A₂), [b₁; b₂]⟩_H`. | [`IneqsAddEqProjection.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsAddEqProjection.lean) — the projection as an image | `correct` |
| `Eq. 27` | `⟨A₁, b₁⟩_H ⊖ P₂ = ⟨A₁, b*⟩_H`, `b*(j) = b₁(j) - ρ(P₂, A₁(j,·)ᵀ)` [25, Thm. 2.2], for arbitrary subtrahends; `P₂ = ∅` gives `ℝⁿ`. | [`MinkowskiDiffIneqsEq.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/MinkowskiDiffIneqsEq.lean) — any set `S`, offsets in the extended reals | `correct` |
| `Eq. 28` | `⟨V₁⟩_V × ⟨V₂⟩_V` is the V-polytope of all stacked pairs of points. | [`CartProd.lean`](../../src/CORALean/ContSet/VPolytope/Real/Operations/CartProd.lean), [`CartProdExact.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/CartProdExact.lean) | `correct` |
| `Eq. 29` | `⟨A₁, b₁⟩_H × ⟨A₂, b₂⟩_H = ⟨blkdiag(A₁, A₂), [b₁; b₂]⟩_H`. | [`IneqsBlockDiagEq.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsBlockDiagEq.lean) | `correct` |
| `Eq. 30` | `conv(⟨V₁⟩_V, ⟨V₂⟩_V) = ⟨[V₁ V₂]⟩_V`. | [`SetLinCombEqConvHull.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SetLinCombEqConvHull.lean), [`SetLinCombConvHull.lean`](../../src/CORALean/ContSet/VPolytope/Real/Counterexamples/SetLinCombConvHull.lean) — with both polytopes nonempty; the counterexample `conv(∅, {0}) = ∅` under [1, Table 3]'s `conv` | `underspecified` — fails only when exactly one operand is empty, by the paper's own definition of `conv`; both operands nonempty is supplied; see Findings |
| `Eq. 31` | `conv(⟨A₁, b₁⟩_H, ⟨A₂, b₂⟩_H) ⊆ ⟨A*, b*⟩_H`, `b*(j) = max{ρ(⟨A₁, b₁⟩_H, A*(j,·)ᵀ), ρ(⟨A₂, b₂⟩_H, A*(j,·)ᵀ)}`, for template directions `A*` [4, Sec. 2]. | [`LinComb.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/LinComb.lean), [`LinCombOfOuter.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/LinCombOfOuter.lean) — with any upper bounds in place of the support function values | `correct` |
| `Eq. 32` | `ρ(⟨[v₁ … vₘ]⟩_V, ℓ) = max_i ℓᵀ vᵢ`. | [`SupportFuncEq.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SupportFuncEq.lean) — `m ≥ 1`; at `m = 0` the polytope is empty and `ρ = -∞` | `correct` |
| `Eq. 33` | `ρ(⟨A, b⟩_H, ℓ) = max ℓᵀ x` s.t. `Ax ≤ b`; `∞` if unbounded in direction `ℓ`, `-∞` if empty. | [`SupportFunc.lean`](../../src/CORALean/ContSet/ContSet/Definitions/SupportFunc.lean) — the definition in the extended reals, both conventions included | `correct` |
| `Eq. 34` | The support vector of a V-polytope is the maximizing point `v_{i*}`. | [`SupportBoundAttained.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SupportBoundAttained.lean), [`SupportFuncEq.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SupportFuncEq.lean) | `correct` |
| `Eq. 35` | The support vector of an H-polytope is the linear program's maximizer; not unique in general; an error for unbounded and empty sets. | n/a — [1, Table 3]'s definition at `Def. 1`; the tree has no H-polytope support vector | `not-a-claim` |
| `Eq. 36` | `⟨A₁, b₁⟩_H ∩ ⟨A₂, b₂⟩_H = ⟨[A₁; A₂], [b₁; b₂]⟩_H`. | [`Intersection.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/Intersection.lean), [`IntersectionExact.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IntersectionExact.lean) | `correct` |
| `Eq. 37` | `P₁ ∪ P₂ ⊆ conv(P₁, P₂)`, computed by (30)-(31). | [`UnionSubsetSetLinComb.lean`](../../src/CORALean/ContSet/ContSet/Theorems/UnionSubsetSetLinComb.lean), [`SetLinCombConvHull.lean`](../../src/CORALean/ContSet/VPolytope/Real/Counterexamples/SetLinCombConvHull.lean) — for nonempty operands; `∅ ∪ {0}` is not in `conv(∅, {0}) = ∅` | `underspecified` — fails only when exactly one operand is empty, under [1, Table 3]'s `conv`; both operands nonempty is supplied; see Findings |
| `Alg. 3` | Random bounded, non-degenerate H-polytopes: the simplex `[Iₙ -(1/√n) 1]ᵀ x ≤ 1`, extra rows `ℓ x ≤ 1` for directions sampled from the unit ball, then `M ⟨A, b⟩_H + z` for invertible `M`; "any direction `ℓ` of unit length and with an associated offset of `1` will be non-redundant". | [`SimplexRows.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/SimplexRows.lean), [`GenerateRandomH.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/GenerateRandomH.lean), [`GenerateRandomHBoundedFullDim.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/GenerateRandomHBoundedFullDim.lean), [`IneqsUnitRowsMinimal.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsUnitRowsMinimal.lean), [`SimplexRowsRedundant.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/SimplexRowsRedundant.lean) — the directions as arguments; bounded and non-degenerate for `‖ℓ‖₂ ≤ 1`. Distinct unit rows are all non-redundant; `ℓ = e₁` repeats a simplex row | `underspecified` — a unit direction equal to a row already present is redundant; the claim needs `ℓ` distinct from them; see Findings |
| `Sec. 4 (complexity)` | The running times stated with each operation, e.g. `O(h LP(n, h))` for `Eq. 1`, `O(m₁ LP(m₂, n))` for `Eq. 3`, `O(n LP(n, h))` for `Eq. 16`, `O(nr LP(n + r_max, h + r_max))` for `Alg. 2`, `O(1)` for `Eq. 29`, `Eq. 30` and `Eq. 36`. | n/a — running times stated beside the operations in prose (the paper's "computational complexity" analysis, with `LP(p, q)` the cost of one linear program), never as a Proposition or Theorem. A Lean definition says what is computed and not what computing it costs, so the tree can only assert such a bound under `Complexity/Time/` and never prove it; see CONTRIBUTING.md, "A size is proved; a running cost is asserted". The one size in the section, the facet count `O(r^⌊n/2⌋/⌊n/2⌋!)` of Quickhull, is cited from Barber, Dobkin and Huhdanpaa, which has no page here | `not-a-claim` |
| `Fig. 1` | The three steps of `Alg. 3` in `ℝ²`. | n/a — an illustration | `not-a-claim` |
| `Sec. 5` | Comparison with the multi-parametric toolbox on random polytopes of increasing dimension (Table 4). | n/a — an experiment | `not-a-claim` |

## Findings

**Table 1 — the empty set.** Section 3 makes `∅` degenerate and bounded, and the table is read
cell by cell ("cases with more than two properties can be analyzed by using the conjunction over
all pairs"). Then `D ⊕ ND = ND`, `D ⊕ NB = NB`, `ND ⊕ B = ND` and `B ⊕ NB = NB` fail at
`∅ ⊕ ℝⁿ = ∅`, the same four cells of `conv` fail at `conv(∅, ℝⁿ) = ∅` under Table 3's
`conv(S₁, S₂) = {λ s₁ + (1 - λ) s₂}`, and `E ⊖ D = E`, `E ⊖ B = E`, `B ⊖ D = B`, `B ⊖ B = B` fail
at `∅ ⊖ ∅ = ℝⁿ`. The table knows the issue elsewhere: `NE ⊕ D` and `NE ⊕ B` are `–` because the
second summand may be empty. Each failing cell holds once the operand that may be empty is
nonempty. The Cartesian product has `D × NB = D, NB`, which fails at `∅ × ℝ`, and `D × B = D, B`,
which fails outright: the line `{x₂ = 0} ⊂ ℝ²` is degenerate and unbounded, and its product with
the point `{0}` is unbounded. [`AddProperties.lean`](../../src/CORALean/ContSet/ContSet/Counterexamples/AddProperties.lean), [`MinkowskiDiffProperties.lean`](../../src/CORALean/ContSet/ContSet/Counterexamples/MinkowskiDiffProperties.lean), [`ProdProperties.lean`](../../src/CORALean/ContSet/ContSet/Counterexamples/ProdProperties.lean), [`SetLinCombProperties.lean`](../../src/CORALean/ContSet/ContSet/Counterexamples/SetLinCombProperties.lean)

**`Sec. 4.1 (support vector)` — halfspaces tight at the support vector.** To speed up redundancy
removal the paper takes the support vector `ν` of `⟨A*, b*⟩_H` along a redundant halfspace's
normal, calls it a vertex of `⟨A, b⟩_H`, and concludes that every other halfspace with
`A(k,·) ν = b(k)` is non-redundant. A halfspace can touch a vertex without defining a facet: the
unit square with the extra rows `x + y ≤ 2` and `x + y ≤ 3` has `x + y ≤ 3` redundant, its
support vector the corner `(1, 1)`, and `x + y ≤ 2` tight there and redundant too. Nor need `ν` be
a vertex: a linear program maximizing along an edge's normal may return any point of that edge.
[`TightRedundant.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/TightRedundant.lean)

**`Sec. 4.1 (interval hull)` — an empty polytope.** Removing all halfspaces that strictly contain
the interval hull is sound for a nonempty polytope (for any enclosure in place of the hull). For
an empty one the hull is empty and every halfspace qualifies: `{x ≤ 0, -x ≤ -1}` without `x ≤ 0`
is `{x ≥ 1}`. [`IneqsEqOfStrict.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsEqOfStrict.lean), [`IneqsEqOfStrict.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IneqsEqOfStrict.lean)

**`Eq. 7` — repeated points.** Redundancy in the sense of `Eq. 2` drops one index, so a point
listed twice is redundant by its copy. `⟨[0 0]⟩_V = {0}` and `⟨[1 1]⟩_V = {1}` then pass the test
on both sides. With distinct points a non-redundant point is an extreme point, which the other
list must contain, and the test is exact. CORA compacts both lists before comparing them, which
removes the repetition. [`ConstructEqIffOfInjective.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/ConstructEqIffOfInjective.lean), [`ConstructEqIff.lean`](../../src/CORALean/ContSet/VPolytope/Real/Counterexamples/ConstructEqIff.lean)

**`Alg. 1` — line 4.** The listing returns `⊥` when a row has no partner and
`ρ(⟨A₁*, b₁*⟩_H, A₁(j,·)ᵀ) = b₁(j)`, which says the row is redundant — something no row of the
minimal representation the algorithm requires can be. So the printed test never fails:
`[0, 1] = {x ≤ 1, -x ≤ 0}` and `[0, 2]` are minimal, normalized and non-degenerate, `x ≤ 1` and
`x ≤ 2` have no partners, and the support function without them is `+∞`, so the listing returns
`⊤`. The text says what is meant: an unmatched row "must be redundant for set equality to hold";
CORA's `aux_isNonredundantConstraint` tests exactly that, and so does `isequalNondeg`. With that
reading the test decides equality, by the uniqueness of the normalized facet rows of a
non-degenerate polytope. The minimal representation is needed: a repeated row passes as
redundant by its copy, which CORA does not exclude ([`polytope` `isequal`](../coverage/contSet/polytope.md)). [`IsequalNondegPrinted.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IsequalNondegPrinted.lean), [`IsequalNondegIff.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IsequalNondegIff.lean), [`IsequalNondegDuplicate.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IsequalNondegDuplicate.lean)

**`Eq. 9` — the optimal value.** `min bᵀ y` over the cone `Aᵀ y = 0`, `y ≥ 0` is `0` or `-∞`, so
"feasible with `y* < 0`" is read as Farkas' alternative: some feasible `y` has `bᵀ y < 0`. [`IneqsEqEmptyIff.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsEqEmptyIff.lean)

**`Eq. 18` — the comparison.** The display reads `degenerate(⟨A, b⟩_H) ← ⊤ if r > 0`; the sentence
after it, "if the radius of the Chebyshev ball is `0`, then the polytope must be degenerate", is
the correct test. `[0, 1]` admits the radius `1/2` and has an interior. [`InteriorNonemptyIffChebyshev.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/InteriorNonemptyIffChebyshev.lean), [`IneqsDegenerateChebyshev.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/IneqsDegenerateChebyshev.lean)

**`Eq. 20` — QR without pivoting.** The first `r = rank V̄` columns of `Q` in `QR = V̄` span the
column space of `V̄` only when the first `r` columns of `V̄` are independent, which a QR
decomposition with column pivoting arranges. For the points `±e₁, ±e₃` the mean is `0`,
`V̄ = [e₁ -e₁ e₃ -e₃]` has rank `2`, and `Q = I`, `R = V̄` is a QR decomposition whose first two
columns miss `e₃`. CORA's `priv_isFullDim_V` takes `qr` without pivoting ([`polytope` `isFullDim`](../coverage/contSet/polytope.md)). [`SpanQrCols.lean`](../../src/CORALean/ContSet/VPolytope/Real/Counterexamples/SpanQrCols.lean), [`SpanQrColsEqOfIndep.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SpanQrColsEqOfIndep.lean)

**`Alg. 2` — orthonormal.** Line 8 appends `x_iter` itself, a maximizer of `‖x‖∞`, so the columns
are orthogonal, not orthonormal as the comment says; nothing downstream needs more. The maximizer
of (22) and the cap `φ` for unbounded polytopes are specified only by the program, and are an
argument with that specification here; at `ε = 0` the result spans exactly the direction of the
affine hull, and at `ε > 0` every point is within `ε` of the span. [`AffineHullBasisSpec.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/AffineHullBasisSpec.lean)

**`Eq. 24` — the dimensions.** With `M ∈ ℝ^{m×n}` of rank `r`, the display has `D ∈ ℝ^{(m-r)×n}`
where `D` is the `r × r` block of singular values, `Iₙ` where the identity block of `[D⁻¹ 0; 0 I]`
is `I_{n-r}`, and `U [I_r 0]` (an `m × n` product only if `m = r`) where `U [I_r 0; 0 0]` is meant.
The identity holds for any factorization `M = U E S Vᵀ` with `V` orthogonal and `S` invertible. [`ImageIneqsOfFactor.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ImageIneqsOfFactor.lean)

**`Eq. 30` and `Eq. 37` — an empty operand.** Table 3 defines `conv(S₁, S₂)` by segments between
points of both sets, and Table 1 accordingly has `conv(E, ·) = E`. Then `conv(⟨[]⟩_V, ⟨[0]⟩_V)` is
empty, while the concatenated list `⟨[0]⟩_V` of `Eq. 30` is `{0}`, and the union `∅ ∪ {0}` of
`Eq. 37` is not inside it. CORA's `convHull_` follows Table 3 and returns the empty polytope. With
both operands nonempty both equations hold. [`SetLinCombEqConvHull.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/SetLinCombEqConvHull.lean), [`SetLinCombConvHull.lean`](../../src/CORALean/ContSet/VPolytope/Real/Counterexamples/SetLinCombConvHull.lean)

**`Alg. 3` — a redundant unit direction.** "Any direction `ℓ` of unit length and with an associated
offset of `1` will be non-redundant" fails when `ℓ` is a row already present: in `ℝ¹` the simplex
is `{x ≤ 1, -x ≤ 1}` and `ℓ = 1` repeats `x ≤ 1`. When all rows are distinct unit vectors with
offset `1`, none is redundant. Line 3 samples from the unit ball, not its surface; the output is
bounded and non-degenerate either way. [`IneqsUnitRowsMinimal.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/IneqsUnitRowsMinimal.lean), [`SimplexRowsRedundant.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/SimplexRowsRedundant.lean)

**`Sec. 3 (minimal representation)` — a property of the representation.** "Empty sets are ...
in minimal representation", minimal meaning "represented by a minimal amount of halfspaces or
points". Minimality belongs to a representation, and the empty set has many. Every
V-representation of `∅` lists no points, since a listed point lies in the hull, so it is minimal
([`KEqZeroOfConstructEqEmpty.lean`](../../src/CORALean/ContSet/VPolytope/Real/Theorems/KEqZeroOfConstructEqEmpty.lean)).
CORA's H-representation of `∅`, the single row `0 ≤ -1`, has the fewest rows any H-representation of
`∅` can have, since with none every point satisfies the system
([`EmptySetRowsMinimal.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/EmptySetRowsMinimal.lean)).
But `x ≤ -1, -x ≤ -1, x ≤ 5` is also `∅`, and its third row is redundant in the sense of `Eq. 1`
([`EmptyRedundant.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/EmptyRedundant.lean)).
The sentence is right about the representations CORA keeps for `∅`, and that is how the row
reads it.
