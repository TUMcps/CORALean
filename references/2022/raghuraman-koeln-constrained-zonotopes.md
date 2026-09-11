# Set operations and order reductions for constrained zonotopes

V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.

**Source:** https://ar5iv.labs.arxiv.org/html/2009.06039 (arXiv v1 — the only version arXiv has; no v2 was ever posted even though the paper was later published in Automatica 139 (2022) 110204, which is paywalled and could not be read)  
**Inventory:** partial — confirmed against arXiv v1 only; the published Automatica numbering could NOT be verified and appears to differ (see notes)

Operations on constrained zonotopes, and what each costs in generators and
constraints. `ConZonotope.linComb` is the one used here.

**Two numberings.** The arXiv preprint runs one counter across Lemmas,
Theorems, Definitions and Remarks; the published version numbers Theorems on
their own. The tree cites `Thm. 5`, which is the published numbering — the
preprint calls the same result Theorem 19 — so the entry names Automatica. The
table below is the preprint's labels, which is what can be read.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Lemma 1` | [cites Scott et al., Section 5.1] The zonotope Z={G,c} intersects hyperplane H={x\|h^Tx=f} iff \|f-h^Tc\| ≤ Σ\|h^Tg_i\| (eq. 4); if so, the intersection with the corresponding halfspace is representable in CG-Rep by adding exactly one generator and one equality constraint. | — |
| `Thm. 2` | If zonotope Z intersects hyperplane H (per Lemma 1), the intersection Z_h = Z∩H₋ with the halfspace H₋ is a constrained zonotope, with an explicit generator/constraint formula (eq. 5). | — |
| `Lemma 4` | The constrained zonotope Z_c={G,c,A,b} intersects hyperplane H={x\|h^Tx=f} if f_min ≤ f ≤ f_max, where f_min/f_max are the min/max of h^T(c+Gξ) subject to \|ξ\|∞≤1, Aξ=b. | — |
| `Thm. 7` | Gives a sufficient condition (existence of indices r,c with a_{r,c}≠0 and R_{r,c}⊆[-1,1], eq. 12, using E_k from Algorithm 1) under which a constrained zonotope Z_c can be exactly represented by a constrained zonotope with one fewer constraint (constraint elimination / redundancy removal). | — |
| `Lemma 10` | [cites Sadraddini & Tedrake, Thm. 3] Given zonotopes X={G_x,c_x}, Y={G_y,c_y}, X⊆Y if there exist Γ, β satisfying G_x=G_yΓ, c_y-c_x=G_yβ, \|Γ\|·1+\|β\|≤1 (a sufficient zonotope-containment condition). | — |
| `Thm. 11` | Gives a sufficient condition for a reduced-order zonotope Z_r={G_r,c} (with G_r=GT, T entries in {-1,0,1}) to be an inner-approximation Z_r⊆Z of the original zonotope Z={G,c}. | — |
| `Def. 13` | [cites Sadraddini & Tedrake] An AH-polytope X⊂R^n is an affine transformation X = x̄ + XP of an H-Rep polytope P⊂R^m (eq. 16). | — |
| `Thm. 14` | A non-empty set Z_c⊂R^n is a constrained zonotope if and only if it is an AH-polytope (equivalence of the two representations, with an explicit conversion using Theorem 1 of [18] for one direction). | — |
| `Lemma 16` | [cites Sadraddini & Tedrake, Thm. 1] Sufficient condition (via Γ, β and the halfspace matrices of the underlying polytopes) for containment X⊆Y of two AH-polytopes. | — |
| `Def. 18` | [cites [15]] The convex hull of the union of two polytopes P1,P2: CH(P1∪P2) := {x1λ+x2(1-λ) \| x1∈P1,x2∈P2,0≤λ≤1}. | n/a — the convex hull of a union, a classical definition the paper restates; `ContSet.segments` is it |
| `Thm. 19` | The convex hull of the union of two constrained zonotopes Z1, Z2 is itself a constrained zonotope Z_h, with an explicit closed-form construction of G_h, c_h, A_h, b_h. | n/a — the preprint's number for `Thm. 5`, the same result under the other numbering |
| `Thm. 5` | (published numbering; the preprint calls it Theorem 19) The convex hull of the union of two constrained zonotopes is a constrained zonotope, with an explicit generator and constraint formula. | [`LinComb.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Complexity/LinComb.lean), [`LinComb.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/LinComb.lean) |
| `Def. 21` | [cites [35]] A set Ω⊂R^n is a robust positively invariant (RPI) set of a linear system x⁺=Ax⊕w if AΩ⊕W⊆Ω. | — |
| `Def. 22` | [cites [11]] The minimal RPI (mRPI) set F∞ of the system is the RPI set contained in every closed RPI set, given by F∞ = ⊕_{i=0}^∞ A^i W (eq. 26). | — |
| `Thm. 23` | Gives a sufficient condition (existence of Γ1, Γ2, β satisfying certain matrix equalities) for a zonotope Z={GΦ,c} (Φ=diag(φ), φ>0) to be an RPI set of the system, given disturbance zonotope W. | — |
| `Def. 25` | [cites [36]] The Pontryagin difference Z_d = Z1 ⊖ Z2 := {z∈R^n \| z⊕Z2⊆Z1} (eq. 30); also called the Minkowski difference or erosion. | n/a — the Pontryagin difference, a classical definition the paper restates; `ContSet.minkowskiDiff` is it |
| `Lemma 26` | [cites [36], Thm. 1] For zonotopes Z1={G1,c1}, Z2={G2,c2}, the exact Pontryagin difference Z_d=Z1⊖Z2 is computed by the recursion Z_int^(0)=Z1-c2, Z_int^(i) = (Z_int^(i-1)+g_{2,i}) ∩ (Z_int^(i-1)-g_{2,i}) over the generators of Z2. | — |
| `Thm. 27` | Given zonotopes Z1, Z2, gives a sufficient condition (existence of Γ, and a diagonal scaling Φ) for Z̃_d = {[G1 G2]Φ, c_d} to be an inner-approximation Z̃_d ⊆ Z1⊖Z2 of the Pontryagin difference. | — |
