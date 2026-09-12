# Constrained Polynomial Zonotopes

N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
2023.

**Source:** https://ar5iv.labs.arxiv.org/html/2005.08849  
**Inventory:** confirmed

Polynomial zonotopes with polynomial constraints on their factors, which is
what makes intersection exact. The `ConPolyZono` representation.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Zonotope) [cites Girard 2005, Def. 1] Z := {c + Σ α_k G_(·,k) \| α_k∈[-1,1]}, shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Def. 2` | (Constrained Zonotope) [cites Scott et al. 2016, Def. 3] CZ := {c + Σ α_k G_(·,k) \| Σ α_k A_(·,k) = b, α_k∈[-1,1]}. | n/a — restated from Scott et al. 2016, which this formalization does not draw on directly |
| `Def. 3` | (Polynomial Zonotope) [cites Kochdumper & Althoff 2019, Def. 1] PZ := {c + Σ_i (Π_k α_k^E(k,i)) G_(·,i) \| α_k∈[-1,1]} (here the constant offset c is kept separate from the generator matrix, unlike the cited definition). | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Def. 4` | (Ellipsoid) [cites Boyd & Vandenberghe 2004, Eq. 2.3] E := {x \| (x-c)^T Q^{-1} (x-c) ≤ 1} for symmetric positive-definite Q; shorthand ⟨c,Q⟩_E. | n/a — restated from Boyd and Vandenberghe 2004, which this formalization does not draw on directly |
| `Def. 5` | (Constrained Polynomial Zonotope) CPZ := {c + Σ_i (Π_k α_k^E(k,i)) G_(·,i) \| Σ_i (Π_k α_k^R(k,i)) A_(·,i) = b, α_k∈[-1,1]}, the paper's central new set representation. | [`ConPolyZono.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/ConPolyZono.lean) |
| `Prop. 1` | (Compact Generators) compactGen(CPZ) returns a CPZ representation with a regular (duplicate-free) exponent matrix, by merging generators with identical exponent columns; complexity O(ph·log(h)+nh). | [`CompactGensExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/CompactGensExact.lean) |
| `Prop. 2` | (Compact Constraints) compactCon(CPZ) returns a CPZ with a regular constraint exponent matrix, analogous to Prop. 1 but for the constraint part; complexity O(pq·log(q)+mq). | [`CompactConsExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/CompactConsExact.lean) |
| `Lemma 1` | (Lifted Polynomial Zonotope) The lifted polynomial zonotope PZ^+ = ⟨[c;-b],[[G,0];[0,A]],[E R]⟩_PZ in R^{n+m} satisfies x∈CPZ ⇔ [x;0]∈PZ^+, i.e. CPZ is the "slice" of PZ^+ where the lifted coordinates vanish. | — |
| `Def. 6` | (Contractor) [cites Jaulin et al. 2006, Ch. 4.1] contract(f(x),I) ⊆ I and ∀x∈I: f(x)=0 ⇒ x∈contract(f(x),I), a standard interval-contractor definition used later for constraint solving/tightening. | n/a — restated from Jaulin et al. 2006, which this formalization does not draw on directly |
| `Prop. 3` | (Conversion Ellipsoid) An ellipsoid E=⟨c,Q⟩_E can be equivalently represented as a CPZ, using an eigendecomposition Q=VΛV^T of Q for the generator matrix. | [`Ellipsoid_to_ConPolyZono.lean`](../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_ConPolyZono.lean) |
| `Prop. 4` | (Constrained Zonotope Enclosure) conZono(CPZ) returns a constrained zonotope CZ ⊇ CPZ, obtained by lifting to PZ^+ (Lemma 1), compacting, and enclosing by a zonotope (zono operator). | — |
| `Prop. 5` | (Linear Map) M⊗CPZ = ⟨Mc,MG,E,A,b,R⟩_CPZ; complexity O(wμ) in representation size μ, O(wn²) in dimension n; regularity is preserved. | [`MtimesExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/MtimesExact.lean) |
| `Prop. 6` | (Minkowski Sum) CPZ1 ⊕ CPZ2 = ⟨c1+c2,[G1 G2],block-diag(E1,E2),block-diag(A1,A2),[b1;b2],block-diag(R1,R2)⟩_CPZ. | [`PlusExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/PlusExact.lean) |
| `Prop. 7` | (Cartesian Product) CPZ1 × CPZ2 formula analogous to Prop. 6 but stacking centers and block-diagonalizing all matrices for the product set. | [`CartProdExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/CartProdExact.lean) |
| `Prop. 8` | (Linear Combination) Gives comb(CPZ1,CPZ2), the CPZ representing {0.5(1+λ)x1+0.5(1-λ)x2 \| x1∈CPZ1,x2∈CPZ2,λ∈[-1,1]} as an explicit generator/exponent/constraint construction. | [`LinCombExactOfDependent.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/LinCombExactOfDependent.lean) |
| `Prop. 9` | (Convex Hull) conv(CPZ1,CPZ2) formula, extending comb (Prop. 8) with an extra scaling factor variable a to obtain the actual convex hull rather than just the linear combination. | — |
| `Prop. 10` | (Quadratic Map) Gives sq(Q,CPZ) for a discrete set of matrices Q={Q1,...,Qw}, as a CPZ with new generator/exponent columns built from pairwise products of the original dependent generators. | [`QuadMapExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/QuadMapExact.lean) |
| `Prop. 11` | (Intersection) CPZ1 ∩ CPZ2 = ⟨c1,G1,[E1;0],block-arranged A with G1,-G2 coupling,[b1;b2;c2-c1],[R1,0;0,R2;E1,0;0,E2]⟩_CPZ — encodes the intersection by adding a constraint that the two representations describe the same point. | [`IntersectionExact.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/IntersectionExact.lean) |
| `Thm. 1` | (Union) Gives an explicit closed-form CPZ representation of CPZ1 ∪ CPZ2, using an extra binary-like factor to select between the two operands (center 0.5(c1+c2), and block-structured G, E, A, b, R). Proof in Appendix A, using Def. 7, Lemma 2, Prop. 14. | — |
| `Prop. 12` | (Order Reduction) reduce(CPZ,ρ_d) for a desired order ρ_d ≥ 2(n+m)/n returns a CPZ of order ≤ ρ_d enclosing CPZ, by partitioning generators/constraints into a kept set H and a reduced set K. | [`ReduceOuter.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/ReduceOuter.lean) |
| `Prop. 13` | (Constraint Reduction) Given a constraint index r and indices d,s satisfying a matching condition (eq. 33) between E and R, reduceCon(CPZ,r,d,s) removes constraint r and returns an enclosing CPZ. | — |
| `Def. 7` | (Appendix A) Given constraint data A,b,R, constrDom(A,b,R) := {α \| Σ_i (Π_k α_k^R(k,i)) A_(·,i) = b, α_k∈[-1,1]}, the set of factor values satisfying the CPZ's constraint — used in the proof of Thm. 1. | [`Domain.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Operations/Domain.lean) |
| `Lemma 2` | (Appendix A) For domains D1,D2 ⊆ [-1,1]^p, the polynomial-zonotope-style set over D1∪D2 equals the union of the sets over D1 and D2 separately (splits a CPZ's defining set by splitting its constraint domain) — used in the proof of Thm. 1. | [`DependentSetUnionDomain.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/DependentSetUnionDomain.lean) |
| `Prop. 14` | (Appendix A) (Subset) Given CPZ, a factor index r, and an interval [l,u]⊆[-1,1], subset(CPZ,r,l,u) restricts/substitutes the domain of factor α_r to [l,u], giving a CPZ representing a subset of the original — used in the proof of Thm. 1. | — |

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`API.lean`](../../src/CORALean/ContSet/ConPolyZono/API.lean)
* [`HoldsPointIff.lean`](../../src/CORALean/ContSet/ConPolyZono/Real/Theorems/HoldsPointIff.lean)
