# Set operations and order reductions for constrained zonotopes

V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.

**Source:** https://arxiv.org/pdf/2009.06039 (the PDF; arXiv v1 is the only version arXiv has — no v2 was ever posted, even though the paper was later published in Automatica 139 (2022) 110204, which is paywalled and could not be read)  
**Inventory:** confirmed — against the arXiv v1 PDF; the published Automatica typesetting itself was not obtained, but see below for why its numbering is not believed to differ

There is no second numbering. This page used to say the arXiv preprint ran a
single counter across Lemmas, Theorems, Definitions and Remarks (`Lemma 4`,
`Thm. 7`, `Lemma 10`, `Thm. 11`, `Def. 13`, `Thm. 14`, `Lemma 16`, `Def. 18`,
`Thm. 19`, `Def. 21`, `Def. 22`, `Thm. 23`, `Def. 25`, `Lemma 26`, `Thm. 27`),
with the published version numbering Theorems on their own — inherited from
an ar5iv-based inventory. The arXiv **PDF** contradicts this outright: it
never prints "Theorem 19", "Lemma 10", "Def. 13", or any of the other
double-digit labels, anywhere. Every one of Definition, Lemma and Theorem
instead has its own separate counter (Def. 1–5, Lemma 1–5, Theorem 1–7), and
that is what the table below now records. The old "preprint" numbers are
exactly the position each result would fall at under a *single* counter
spanning Definitions, Lemmas, Theorems, Remarks and Examples (but not
Algorithms, which are numbered separately again) in reading order — i.e.
they are ar5iv's cross-reference numbering, corrupted by merging
distinct counters into one, the same failure mode already found in
Kochdumper's HSCC paper — not a real second numbering. The tree's citation,
`[1, Thm. 5]`, already used the PDF's real number, so no `.lean` file needed
a change.

Operations on constrained zonotopes, and what each costs in generators and
constraints. `ConZonotope.linComb` is the one used here.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Lemma 1` | [cites Scott et al., Section 5.1] The zonotope Z={G,c} intersects hyperplane H={x\|h^Tx=f} iff \|f-h^Tc\| ≤ Σ\|h^Tg_i\| (eq. 4); if so, the intersection with the corresponding halfspace is representable in CG-Rep by adding exactly one generator and one equality constraint. | — |
| `Thm. 1` | If zonotope Z intersects hyperplane H (per Lemma 1), the intersection Z_h = Z∩H₋ with the halfspace H₋ is a constrained zonotope, with an explicit generator/constraint formula (eq. 5). | — |
| `Lemma 2` | The constrained zonotope Z_c={G,c,A,b} intersects hyperplane H={x\|h^Tx=f} if f_min ≤ f ≤ f_max, where f_min/f_max are the min/max of h^T(c+Gξ) subject to \|ξ\|∞≤1, Aξ=b. | — |
| `Thm. 2` | Gives a sufficient condition (existence of indices r,c with a_{r,c}≠0 and R_{r,c}⊆[-1,1], eq. 12, using E_k from Algorithm 1) under which a constrained zonotope Z_c can be exactly represented by a constrained zonotope with one fewer constraint (constraint elimination / redundancy removal). | — |
| `Lemma 3` | [cites Sadraddini & Tedrake, Thm. 3] Given zonotopes X={G_x,c_x}, Y={G_y,c_y}, X⊆Y if there exist Γ, β satisfying G_x=G_yΓ, c_y-c_x=G_yβ, \|Γ\|·1+\|β\|≤1 (a sufficient zonotope-containment condition). | — |
| `Thm. 3` | Gives a sufficient condition for a reduced-order zonotope Z_r={G_r,c} (with G_r=GT, T entries in {-1,0,1}) to be an inner-approximation Z_r⊆Z of the original zonotope Z={G,c}. | — |
| `Def. 1` | [cites Sadraddini & Tedrake] An AH-polytope X⊂R^n is an affine transformation X = x̄ + XP of an H-Rep polytope P⊂R^m (eq. 16). | — |
| `Thm. 4` | A non-empty set Z_c⊂R^n is a constrained zonotope if and only if it is an AH-polytope (equivalence of the two representations, with an explicit conversion using Theorem 1 of [18] for one direction). | — |
| `Lemma 4` | [cites Sadraddini & Tedrake, Thm. 1] Sufficient condition (via Γ, β and the halfspace matrices of the underlying polytopes) for containment X⊆Y of two AH-polytopes. | — |
| `Def. 2` | [cites [15]] The convex hull of the union of two polytopes P1,P2: CH(P1∪P2) := {x1λ+x2(1-λ) \| x1∈P1,x2∈P2,0≤λ≤1}. | n/a — the convex hull of a union, a classical definition the paper restates; `ContSet.segments` is it |
| `Thm. 5` | The convex hull of the union of two constrained zonotopes Z1, Z2 is itself a constrained zonotope Z_h, with an explicit closed-form construction of G_h, c_h, A_h, b_h. | [`LinComb.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Complexity/LinComb.lean), [`LinComb.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/LinComb.lean) |
| `Def. 3` | [cites [35]] A set Ω⊂R^n is a robust positively invariant (RPI) set of a linear system x⁺=Ax⊕w if AΩ⊕W⊆Ω. | — |
| `Def. 4` | [cites [11]] The minimal RPI (mRPI) set F∞ of the system is the RPI set contained in every closed RPI set, given by F∞ = ⊕_{i=0}^∞ A^i W (eq. 26). | — |
| `Thm. 6` | Gives a sufficient condition (existence of Γ1, Γ2, β satisfying certain matrix equalities) for a zonotope Z={GΦ,c} (Φ=diag(φ), φ>0) to be an RPI set of the system, given disturbance zonotope W. | — |
| `Def. 5` | [cites [36]] The Pontryagin difference Z_d = Z1 ⊖ Z2 := {z∈R^n \| z⊕Z2⊆Z1} (eq. 30); also called the Minkowski difference or erosion. | n/a — the Pontryagin difference, a classical definition the paper restates; `ContSet.minkowskiDiff` is it |
| `Lemma 5` | [cites [36], Thm. 1] For zonotopes Z1={G1,c1}, Z2={G2,c2}, the exact Pontryagin difference Z_d=Z1⊖Z2 is computed by the recursion Z_int^(0)=Z1-c2, Z_int^(i) = (Z_int^(i-1)+g_{2,i}) ∩ (Z_int^(i-1)-g_{2,i}) over the generators of Z2. | — |
| `Thm. 7` | Given zonotopes Z1, Z2, gives a sufficient condition (existence of Γ, and a diagonal scaling Φ) for Z̃_d = {[G1 G2]Φ, c_d} to be an inner-approximation Z̃_d ⊆ Z1⊖Z2 of the Pontryagin difference. | — |
