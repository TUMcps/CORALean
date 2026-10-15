# Constrained Polynomial Zonotopes

N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
2023.

**Source:** https://arxiv.org/pdf/2005.08849 (the PDF, read with `pypdf`; poppler is not
installed. The page was seeded from ar5iv, which renumbers results and has corrupted four of
our six ar5iv-sourced pages — but `Def. 5`, `Prop. 8`, `Prop. 9`, `Prop. 13`, `Prop. 14`,
`Thm. 1`, eq. (4) and eq. (27)-(28) were all checked against the PDF and agree, so this page
is not one of the corrupted ones)  
**Inventory:** confirmed

Polynomial zonotopes with polynomial constraints on their factors, which is
what makes intersection exact. The `ConPolyZono` representation.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotope) [cites Girard 2005, Def. 1] Z := {c + Σ α_k G_(·,k) \| α_k∈[-1,1]}, shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Def. 2` | (Constrained Zonotope) [cites Scott et al. 2016, Def. 3] CZ := {c + Σ α_k G_(·,k) \| Σ α_k A_(·,k) = b, α_k∈[-1,1]}. | n/a — restated from Scott et al. 2016, which this formalization does not draw on directly | `restated` |
| `Def. 3` | (Polynomial Zonotope) [cites Kochdumper & Althoff 2019, Def. 1] PZ := {c + Σ_i (Π_k α_k^E(k,i)) G_(·,i) \| α_k∈[-1,1]} (here the constant offset c is kept separate from the generator matrix, unlike the cited definition). | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) | `restated` |
| `Def. 4` | (Ellipsoid) [cites Boyd & Vandenberghe 2004, Eq. 2.3] E := {x \| (x-c)^T Q^{-1} (x-c) ≤ 1} for symmetric positive-definite Q; shorthand ⟨c,Q⟩_E. | n/a — restated from Boyd and Vandenberghe 2004, which this formalization does not draw on directly | `restated` |
| `Def. 5` | (Constrained Polynomial Zonotope) CPZ := {c + Σ_i (Π_k α_k^E(k,i)) G_(·,i) \| Σ_i (Π_k α_k^R(k,i)) A_(·,i) = b, α_k∈[-1,1]}, the paper's central new set representation. | [`ConPolyZono.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/ConPolyZono.lean) — carries an independent block `GI`, which Def. 5 has none of, and an `Interval` `b` where Def. 5 has a crisp vector ([the coverage README, departures from CORA](../coverage/README.md#departures-from-cora-that-belong-to-no-single-method)). **As printed:** Def. 5's set is `construct` at `q = 0` and the point interval `[b, b]`, where `b.inf ≤ Aμ(α) ≤ b.sup` is the printed `Aμ(α) = b` | `correct` |
| `Prop. 1` | (Compact Generators) compactGen(CPZ) returns a CPZ representation with a regular (duplicate-free) exponent matrix, by merging generators with identical exponent columns. | [`CompactGensExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/CompactGensExact.lean) | `correct` |
| `Prop. 1 (complexity)` | compactGen(CPZ) has complexity O(ph·log(h)+nh). | n/a — a running time stated of the construction, which the tree can only assert (`Complexity/Time/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Prop. 2` | (Compact Constraints) compactCon(CPZ) returns a CPZ with a regular constraint exponent matrix, analogous to Prop. 1 but for the constraint part. | [`CompactConsExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/CompactConsExact.lean) | `correct` |
| `Prop. 2 (complexity)` | compactCon(CPZ) has complexity O(pq·log(q)+mq). | n/a — a running time stated of the construction, which the tree can only assert (`Complexity/Time/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Lemma 1` | (Lifted Polynomial Zonotope) The lifted polynomial zonotope PZ^+ = ⟨[c;-b],[[G,0];[0,A]],[E R]⟩_PZ in R^{n+m} satisfies x∈CPZ ⇔ [x;0]∈PZ^+, i.e. CPZ is the "slice" of PZ^+ where the lifted coordinates vanish. | n/a — done differently on purpose: the lift assumes a crisp equality `b`, but [`ConPolyZono.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/ConPolyZono.lean) makes `b` an `Interval` even in this layer, since an equality has no direction to round in. Transferring the biconditional needs an extra slack factor per constraint row absorbing `b`'s width, and — unlike a crisp `b`, which is trivially consistent — that construction only recovers the constraint's meaning (a crossed `b` denoting `∅`) under an added `b.inf ≤ b.sup` hypothesis foreign to the source. That is a different lemma, not this one made more general | `done-differently` |
| `Def. 6` | (Contractor) [cites Jaulin et al. 2006, Ch. 4.1] contract(f(x),I) ⊆ I and ∀x∈I: f(x)=0 ⇒ x∈contract(f(x),I), a standard interval-contractor definition used later for constraint solving/tightening. | n/a — restated from Jaulin et al. 2006, which this formalization does not draw on directly | `restated` |
| `Prop. 3` | (Conversion Ellipsoid) An ellipsoid E=⟨c,Q⟩_E can be equivalently represented as a CPZ, using an eigendecomposition Q=VΛV^T of Q for the generator matrix. | [`EllipsoidConPolyZonoExact.lean`](../../src/CORALean/ContSet/Conversion/Real/Theorems/EllipsoidConPolyZonoExact.lean) — `Ellipsoid` is already in generator form here (`q, G`, not `c, Q`), so no decomposition is needed; exact both ways | `correct` |
| `Prop. 4` | (Constrained Zonotope Enclosure) conZono(CPZ) returns a constrained zonotope CZ ⊇ CPZ, obtained by lifting to PZ^+ (Lemma 1), compacting, and enclosing by a zonotope (zono operator). | n/a — its construction is `Lemma 1`'s, which does not transfer for the same reason; [`ConPolyZono_to_ConZonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/ConPolyZono_to_ConZonotope.lean) explicitly disclaims being it | `done-differently` |
| `Prop. 5` | (Linear Map) M⊗CPZ = ⟨Mc,MG,E,A,b,R⟩_CPZ; regularity is preserved. | [`MtimesExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/MtimesExact.lean) | `correct` |
| `Prop. 5 (complexity)` | The linear map M⊗CPZ has complexity O(wμ) in representation size μ and O(wn²) in dimension n. | n/a — a running time stated of the construction, which the tree can only assert (`Complexity/Time/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Prop. 6` | (Minkowski Sum) CPZ1 ⊕ CPZ2 = ⟨c1+c2,[G1 G2],block-diag(E1,E2),block-diag(A1,A2),[b1;b2],block-diag(R1,R2)⟩_CPZ. | [`PlusExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/PlusExact.lean) | `correct` |
| `Prop. 7` | (Cartesian Product) CPZ1 × CPZ2 formula analogous to Prop. 6 but stacking centers and block-diagonalizing all matrices for the product set. | [`CartProdExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/CartProdExact.lean) | `correct` |
| `Prop. 8` | (Linear Combination) Gives comb(CPZ1,CPZ2), the CPZ representing {0.5(1+λ)x1+0.5(1-λ)x2 \| x1∈CPZ1,x2∈CPZ2,λ∈[-1,1]} as an explicit generator/exponent/constraint construction. | [`LinCombExactOfDependent.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/LinCombExactOfDependent.lean) | `correct` |
| `Prop. 9` | (Convex Hull) conv(CPZ1,CPZ2) as a = n+1 copies of comb(CPZ1,CPZ2) (Prop. 8) laid out block-diagonally, plus a fresh factors weighting the copies and one constraint row fixing their sum — definition (4), which is Carathéodory's, with the union replaced by comb. | [`ConvHullExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/ConvHullExact.lean), the construction in [`ConvHull.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/ConvHull.lean) — the equality, under the hypothesis the printed statement omits and is false without; see the finding below | `underspecified` — fails only when exactly one operand is empty (one-dimensional counterexample), which the paper's setting excludes; both nonempty is supplied |
| `Prop. 10` | (Quadratic Map) Gives sq(Q,CPZ) for a discrete set of matrices Q={Q1,...,Qw}, as a CPZ with new generator/exponent columns built from pairwise products of the original dependent generators. | [`QuadMapExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/QuadMapExact.lean) | `correct` |
| `Prop. 11` | (Intersection) CPZ1 ∩ CPZ2 = ⟨c1,G1,[E1;0],block-arranged A with G1,-G2 coupling,[b1;b2;c2-c1],[R1,0;0,R2;E1,0;0,E2]⟩_CPZ — encodes the intersection by adding a constraint that the two representations describe the same point. | [`IntersectionExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/IntersectionExact.lean) | `correct` |
| `Thm. 1` | (Union) Gives an explicit closed-form CPZ representation of CPZ1 ∪ CPZ2, using an extra binary-like factor to select between the two operands (center 0.5(c1+c2), and block-structured G, E, A, b, R). Proof in Appendix A, using Def. 7 and Lemma 2 (Prop. 14 is Appendix B's, for rescaling, and is not used here — see the finding below). | [`UnionExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/UnionExact.lean), the construction in [`Union.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/Union.lean) — the equality, under the hypothesis the printed statement omits and is false without; see the finding below | `underspecified` — fails only when an exponent matrix has an all-zero column (`8 ∉ union`), which the paper's definition of the representation forbids; `NoZeroCol` is supplied |
| `Prop. 12` | (Order Reduction) reduce(CPZ,ρ_d) for a desired order ρ_d ≥ 2(n+m)/n returns a CPZ of order ≤ ρ_d enclosing CPZ, by partitioning generators/constraints into a kept set H and a reduced set K. | n/a — done differently on purpose: the printed reduction and its proof go through `Lemma 1`'s lifted polynomial zonotope, reducing generators and constraints together, and that lift assumes a crisp `b` where [`ConPolyZono.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/ConPolyZono.lean) has an `Interval` ([the coverage README, departures from CORA](../coverage/README.md#departures-from-cora-that-belong-to-no-single-method)), as for `Lemma 1` and `Prop. 4`. The tree reduces `G`/`GI` alone by Girard's rule, boxed into fresh independent generators, with the constraints left to `reduceCon` (`Prop. 13`): [`ReduceOuter.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/ReduceOuter.lean) — the enclosure, [`ReduceOrder.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/ReduceOrder.lean) — its order bound | `done-differently` |
| `Prop. 13` | (Constraint Reduction) Given a constraint index r and indices d,s satisfying a matching condition (eq. 33) between E and R, reduceCon(CPZ,r,d,s) removes constraint r and returns an enclosing CPZ. | [`ReduceConOuter.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/ReduceConOuter.lean), the construction in [`ReduceCon.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/ReduceCon.lean) — the enclosure the statement claims, under one hypothesis this representation needs and the source does not: `b` is an `Interval` here, and the row being solved for a monomial must be a point to determine one. The two cleanups the statement appends, `compactGens` and dropping the all-zero exponent rows, change the representation and not the set, and are not applied | `correct` |
| `Def. 7` | (Appendix A) Given constraint data A,b,R, constrDom(A,b,R) := {α \| Σ_i (Π_k α_k^R(k,i)) A_(·,i) = b, α_k∈[-1,1]}, the set of factor values satisfying the CPZ's constraint — used in the proof of Thm. 1. | [`Domain.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/Domain.lean) | `correct` |
| `Lemma 2` | (Appendix A) For domains D1,D2 ⊆ [-1,1]^p, the polynomial-zonotope-style set over D1∪D2 equals the union of the sets over D1 and D2 separately (splits a CPZ's defining set by splitting its constraint domain) — used in the proof of Thm. 1. | [`DependentSetUnionDomain.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/DependentSetUnionDomain.lean) | `correct` |
| `Prop. 14` | (Appendix B) (Subset) Given CPZ, a factor index r, and an interval [l,u]⊆[-1,1], subset(CPZ,r,l,u) restricts/substitutes the domain of factor α_r to [l,u], giving a CPZ representing a subset of the original — used for rescaling (Sec. 4.4), not for `Thm. 1`: Appendix A's proof of the union never calls `subset`. | [`GetSubset.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/GetSubset.lean), [`GetSubsetConstruct.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/GetSubsetConstruct.lean) — named `getSubset` after CORA's `@conPolyZono/getSubset`, parametrized by `cen, rad` rather than `l, u` (`cen = (l+u)/2`, `rad = (u-l)/2`); see the finding below | `underspecified` — `v₂` divides by zero at `u = −l`, which includes `[−1,1]`; removable, never removed |

## Findings

**Prop. 14 — `v₂` divides by zero on symmetric intervals.** The printed closed form defines
`v₁ = (u+l)/2` and `v₂ = (u−l)/(u+l)` and substitutes `α_r = v₁(1 + v₂ α̂_r)`. The only stated
hypothesis is `[l,u] ⊆ [−1,1]`, so nothing excludes `u = −l` — where `v₂` is a division by zero
and `v₁ v₂` is `0 · undefined` rather than the intended `(u−l)/2`. The cancellation is valid
symbolically but not as an evaluation rule, and the singularity is removable but never removed:
no hypothesis, footnote or remark in the statement, the proof (eqs. 49–50) or the Appendix B
lead-in guards it. The case is not exotic — it includes `[l,u] = [−1,1]`, i.e. `subset` applied
to a factor's own default domain, and every `[−a,a]`. CORA does not inherit the defect: its
`@polyZonotope/getSubset` builds the powers of `a + b·α̂` from `a = center(val)`, `b = rad(val)`
by polynomial convolution and never forms `v₂` at all. The formalization follows CORA and states
the operation in `cen, rad`, which is total.
[`GetSubset.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/GetSubset.lean)

**Prop. 9 — the convex hull identity is false when exactly one operand is empty.**
The proof's step (28), `CPZ1 ∪ CPZ2 ⊆ comb(CPZ1, CPZ2) ⊆ conv(CPZ1, CPZ2)`, is what lets
the union in the definition (4) be replaced by the linear combination, and its left
inclusion needs both operands non-empty: a point of `CPZ1` is a point of `comb` only at
`λ = 1`, which still asks for a point of `CPZ2` to pair it with. Nothing in Def. 5, Prop. 8
or Prop. 9 requires that. The closed form inherits `comb`'s constraint system `a = n+1`
times over, so it is empty whenever either operand is, while (4) reads `s_i ∈ S1 ∪ S2` and
is not. A minimal counterexample in one dimension: `CPZ1` the point `{0}` — no generators,
no factors, no constraints — and `CPZ2` empty, with one factor, one constraint generator,
`A = 1`, `b = 2` and `R = 1`, asking `α = 2` of a factor in `[-1,1]`. Then
`conv(CPZ1, CPZ2)` is `{0}` by (4), while `comb(CPZ1, CPZ2)` is empty and the closed form's
`a` copies of `α = 2` leave it empty too. CORA does not inherit the defect:
`@conPolyZono/convHull_.m` returns the second set outright when the first `representsa_` an
`emptySet`, the same guard `@conPolyZono/or.m` carries for `Thm. 1` — while
`@conPolyZono/linComb.m`, where an empty operand really does empty the result, carries
none. Formalized with that hypothesis added and recorded as a departure: both operands
non-empty, which is exactly what step (28)'s left inclusion asks for and is the weakest
thing that will do, an empty operand emptying the closed form outright. The identity is an
equality, not an enclosure. Definition (4) is Carathéodory's, with exactly `n+1` points, so
the substitution at (28) is the claim that a hull does not grow when its set is enlarged to
anything still inside that hull — Carathéodory's theorem, not an algebraic identity, and
`Global/Caratheodory.lean` proves it over a fixed index, `Mathlib.Analysis.Convex.Caratheodory`
having been brought into the imported surface for it. Unlike `Thm. 1`, no condition on the
exponent matrices enters: every replicated generator column also appears multiplied by its
copy's fresh weight factor, a monomial of degree `1`, so an all-zero column of `E` is
reproduced exactly like any other. One further hypothesis is the representation's rather
than the paper's: neither operand carries independent generators, as Def. 5 has none and
`Prop. 8` is stated the same way.
[`ConvHullExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/ConvHullExact.lean)

**Thm. 1 — the union identity needs both operands' exponent matrices free of all-zero
columns, which the statement never says.** Appendix A.3 argues that on the branch selecting
`CPZ1` (α₁=α₂=1), every term contributed by `CPZ2`'s generator block vanishes, because
`CPZ2`'s own `p2` factors are pinned to `0` there and each such column carries a positive
power of at least one of them. Nothing in Def. 5 or Thm. 1 requires that: a dependent
generator column whose exponent column is all-zero — which is every column whenever
`p2 = 0` — is a monomial of degree `0`, so it equals `1` regardless of which branch pins
the factors, and it gets added on both branches, not just its own. Def. 5 names exactly
this case (`regular` excludes columns that are all-zero, as well as duplicates), and
Props. 5–9 each say "the resulting CPZ is regular if the operands are" — but that is a
claim about the *output*, and Thm. 1 states no such hypothesis on its *inputs*. A minimal
counterexample: `CPZ1` the interval `[-3,3]`, one generator `3` at exponent `1`, and
`CPZ2` the point `{5}`, one generator `5` at exponent `0` and so depending on none of its
own factors. `CPZ1 ∪ CPZ2` is `[-3,3] ∪ {5}`, but Thm. 1's formula at `α1=α2=1` (selecting
`CPZ1`), its own factor `α3=1`, and `CPZ2`'s factor forced to `α4=0`, evaluates to
`3·1+5=8`, which is in neither set. CORA's `@conPolyZono/or.m` builds the identical
matrices and inherits the same gap: it never checks or assumes its two inputs are regular,
and the `compact_(...,'all',eps)` it applies at the end only cleans the *result*, too late
to repair a non-regular *operand*. Formalized with that hypothesis added and recorded as a
departure: `NoZeroCol` on all four exponent matrices, which is weaker than Def. 5's
`regular` — the duplicate-free half never enters Appendix A — and is the weakest condition
on the exponent matrices alone, an all-zero column of `E2` being broken by putting all of
`G2` on it. The identity is an equality, not an enclosure. Two further hypotheses are the
representation's rather than the paper's: neither operand has independent generators, as
Def. 5 has none and `Prop. 8` is stated the same way, and each `b` is non-crossed, which
is automatic where Def. 5's `b` is a crisp vector and is needed here because a crossed `b`
would leave *both* branches unsatisfiable rather than only its own.
[`UnionExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/UnionExact.lean)

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`API.lean`](../../src/CORALean/ContSet/ConPolyZono/API.lean)
* [`ExactPlus.lean`](../../src/CORALean/ContSet/ConPolyZono/Float/Operations/ExactPlus.lean)
* [`ExactPlus.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/ExactPlus.lean)
* [`RepresentsaPoint.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/RepresentsaPoint.lean)
* [`SupportBound.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/SupportBound.lean)
* [`HoldsPointIff.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/HoldsPointIff.lean)
