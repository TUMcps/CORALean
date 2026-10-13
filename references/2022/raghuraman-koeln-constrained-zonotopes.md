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

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Lemma 1` | [cites Girard 2005, Sec. 5.1 — not Scott et al., whose "CG-Rep" is only this page's own name for the representation] The zonotope Z={G,c} intersects hyperplane H={x\|h^Tx=f} iff \|f-h^Tc\| ≤ Σ\|h^Tg_i\| (eq. 4); if so, the intersection with the corresponding halfspace is representable in CG-Rep by adding exactly one generator and one equality constraint. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Thm. 1` | If zonotope Z intersects hyperplane H (per Lemma 1), the intersection Z_h = Z∩H₋ with the halfspace H₋ is a constrained zonotope, with an explicit generator/constraint formula (eq. 5). | [`IntersectHalfspace.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/IntersectHalfspace.lean), [`IntersectHalfspaceExact.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/IntersectHalfspaceExact.lean) — "Z intersects H" taken directly as the hypothesis (`∃ x ∈ Z, h x = f`), as Lemma 1 only restates that condition algebraically | `correct` |
| `Lemma 2` | The constrained zonotope Z_c={G,c,A,b} intersects hyperplane H={x\|h^Tx=f} iff f_min ≤ f ≤ f_max, where f_min/f_max are the min/max of h^T(c+Gξ) subject to \|ξ\|∞≤1, Aξ=b. | [`IntersectsHyperplaneIff.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/IntersectsHyperplaneIff.lean) — f_min/f_max as `IsLeast`/`IsGreatest` of `hᵀ(c + Gξ)` over the feasible `ξ`, which is what the paper's "min"/"max" name | `correct` |
| `Alg. 1` | "Constrained zonotope intervals": computes, row by row of Aξ=b, an interval enclosure E_k of each coefficient's feasible range within B∞(A,b) = {ξ \| Aξ=b, \|ξ\|∞≤1} (used by `Thm. 2`'s eq. 12). | [`RowBound.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/RowBound.lean), [`TightenCoeff.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/TightenCoeff.lean), [`TightenRow.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/TightenRow.lean), [`Tighten.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/Tighten.lean), [`TightenOuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenOuter.lean), [`TightenOuterSafe.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenOuterSafe.lean) — the pass of lines 1-10 over the rows `i = 1..n_c` and columns `j = 1..n_g`, the printed double loop. **As printed:** the paper's `E_j` is `[-1,1] ∩ R_j` after every update (line 5), and `tightenCoeff` meets `E_j` with line 4's bound directly, which is the same `E_j`; `R_j` itself is the other row, `Alg. 1 (R)`. | `correct` |
| `Alg. 1 (R)` | The second output of "Constrained zonotope intervals": R_j ⊃ {ξ_j \| Aξ=b, \|ξ_i\|≤1 ∀ i≠j}, computed beside E_j by R_j ← R_j ∩ (a_ij⁻¹ b_i − Σ_{k≠j} a_ij⁻¹ a_ik E_k) from R_j = [−∞,∞] (line 4), and the emptiness test that follows from it: E ∩ R = ∅ implies Z_c = ∅, so Z_c = ∅ is detected without an LP. | [`TightenCoeffER.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/TightenCoeffER.lean), [`TightenPassER.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/TightenPassER.lean), [`TightenER.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/TightenER.lean), [`TightenEROuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenEROuter.lean), [`TightenEREmpty.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenEREmpty.lean), [`TightenERNotSuperset.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenERNotSuperset.lean) — `ConZonotope.tightenER` runs lines 1-10 with both outputs, `R` from `[−∞, ∞]` in `EReal`. The printed containment fails: on `−2ξ₁ + ξ₂ = 0` it returns `R₂ = [−1, 1]`, while `ξ = (1, 2)` satisfies the row with `\|ξ₁\| ≤ 1`. `R_j` does contain `B∞(A, b)`'s projection (`tightenER_outer`), and that is what the emptiness test needs: `E_j ∩ R_j = ∅` for some `j` gives `Z_c = ∅` (`tightenER_empty`), as printed. **Counterexample:** `ConZonotope.tightenER_not_superset` | `underspecified` — `R_j ⊃ {ξ_j \| Aξ=b, \|ξ_i\|≤1 ∀ i≠j}` fails on a one-row system, because `R_j` is computed from an `E` already tightened with `\|ξ_j\| ≤ 1`; it holds for the projection of `B∞(A, b)`, which carries the emptiness test; an algorithm row, so the correction counts as underspecified; see Findings |
| `Alg. 1 (iteration)` | Algorithm 1 "can be applied iteratively to refine the interval set E": run again on its own output. | [`TightenER.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/TightenER.lean), [`TightenERRefine.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenERRefine.lean), [`TightenEROuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenEROuter.lean), [`TightenERZeroFst.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenERZeroFst.lean) — `tightenER A b k` is `k + 1` passes, each from the previous one's `(E, R)`; one pass is `tighten` (`tightenER_zero_fst`), a further pass returns `E` and `R` inside the previous ones (`tightenER_succ_refine`), and every pass keeps `B∞(A, b)` inside `E` (`tightenER_outer`) | `correct` |
| `Thm. 2` | Gives a sufficient condition (existence of indices r,c with a_{r,c}≠0 and R_{r,c}⊆[-1,1], eq. 12, using E_k from Algorithm 1) under which a constrained zonotope Z_c can be exactly represented by a constrained zonotope with one fewer constraint (constraint elimination / redundancy removal). | [`Eliminate.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/Eliminate.lean), [`EliminateExact.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/EliminateExact.lean) — the identity `Zc = Zr`, under an added dependency-closure hypothesis on a set `S` (the columns row `r` reads besides `c`, `c` excluded, closed under what every row reads from `S`) that the paper's own proof of the `⊆` direction uses and never states | `proof-gap` — the `⊆` direction is asserted in one line and needs a dependency-closure hypothesis the paper never states |
| `Lemma 3` | [cites Sadraddini & Tedrake, Thm. 3] Given zonotopes X={G_x,c_x}, Y={G_y,c_y}, X⊆Y if there exist Γ, β satisfying G_x=G_yΓ, c_y-c_x=G_yβ, \|Γ\|·1+\|β\|≤1 (a sufficient zonotope-containment condition). | n/a — restated from Sadraddini and Tedrake 2019, which this formalization does not draw on directly | `restated` |
| `Thm. 3` | Gives a sufficient condition for a reduced-order zonotope Z_r={G_r,c} (with G_r=GT, T entries in {-1,0,1}) to be an inner-approximation Z_r⊆Z of the original zonotope Z={G,c}. | [`ReduceSignedInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ReduceSignedInner.lean) | `correct` |
| `Def. 1` | [cites Sadraddini & Tedrake] An AH-polytope X⊂R^n is an affine transformation X = x̄ + XP of an H-Rep polytope P⊂R^m (eq. 16). | n/a — restated from Sadraddini and Tedrake 2019, which this formalization does not draw on directly | `restated` |
| `Thm. 4` | A non-empty set Z_c⊂R^n is a constrained zonotope if and only if it is an AH-polytope (equivalence of the two representations, with an explicit conversion using Theorem 1 of [18] for one direction). | [`IsAffineImageIff.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/IsAffineImageIff.lean) — both directions. Boundedness (a `SupportBound` pair per coordinate) is a hypothesis because CORALean's `HPolytope` is a halfspace representation and so admits unbounded sets, whereas the paper's "polytope" already means bounded; it is making the paper's own assumption explicit, not adding one. Non-emptiness is not needed: the equivalence holds at the empty set too, since an infeasible `ConZonotope` denotes `∅` | `correct` |
| `Lemma 4` | [cites Sadraddini & Tedrake, Thm. 1] Sufficient condition (via Γ, β and the halfspace matrices of the underlying polytopes) for containment X⊆Y of two AH-polytopes. | n/a — restated from Sadraddini and Tedrake 2019, which this formalization does not draw on directly | `restated` |
| `Def. 2` | [cites [15]] The convex hull of the union of two polytopes P1,P2: CH(P1∪P2) := {x1λ+x2(1-λ) \| x1∈P1,x2∈P2,0≤λ≤1}. | n/a — the convex hull of a union, a classical definition the paper restates; `ContSet.segments` is it | `restated` |
| `Thm. 5` | The convex hull of the union of two constrained zonotopes Z1, Z2 is itself a constrained zonotope Z_h, with an explicit closed-form construction of G_h, c_h, A_h, b_h. | [`LinComb.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Complexity/Space/LinComb.lean), [`LinComb.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/LinComb.lean) | `correct` |
| `Def. 3` | [cites [35]] A set Ω⊂R^n is a robust positively invariant (RPI) set of a linear system x⁺=Ax⊕w if AΩ⊕W⊆Ω. | n/a — restated from Blanchini 1999, which this formalization does not draw on directly | `restated` |
| `Def. 4` | [cites [11]] The minimal RPI (mRPI) set F∞ of the system is the RPI set contained in every closed RPI set, given by F∞ = ⊕_{i=0}^∞ A^i W (eq. 26). | n/a — restated from Rakovic et al. 2005, which this formalization does not draw on directly | `restated` |
| `Thm. 6` | Gives a sufficient condition (existence of Γ1, Γ2, β satisfying certain matrix equalities) for a zonotope Z={GΦ,c} (Φ=diag(φ), φ>0) to be an RPI set of the system, given disturbance zonotope W. | [`ScaledRPI.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ScaledRPI.lean) — Def. 3's RPI condition (n/a above) restated inline as `A '' Z ⊕ W ⊆ Z`, since it is not carried as a named declaration elsewhere | `correct` |
| `Def. 5` | [cites [36]] The Pontryagin difference Z_d = Z1 ⊖ Z2 := {z∈R^n \| z⊕Z2⊆Z1} (eq. 30); also called the Minkowski difference or erosion. | n/a — the Pontryagin difference, a classical definition the paper restates; `ContSet.minkowskiDiff` is it | `restated` |
| `Lemma 5` | [cites [36], Thm. 1] For zonotopes Z1={G1,c1}, Z2={G2,c2}, the exact Pontryagin difference Z_d=Z1⊖Z2 is computed by the recursion Z_int^(0)=Z1-c2, Z_int^(i) = (Z_int^(i-1)+g_{2,i}) ∩ (Z_int^(i-1)-g_{2,i}) over the generators of Z2. | n/a — restated; tracked as `Thm. 1` on [On Computing the Minkowski Difference of Zonotopes](../2015/althoff-arxiv-minkowski-difference.md) | `restated` |
| `Thm. 7` | Given zonotopes Z1, Z2, gives a sufficient condition (existence of Γ, and a diagonal scaling Φ) for Z̃_d = {[G1 G2]Φ, c_d} to be an inner-approximation Z̃_d ⊆ Z1⊖Z2 of the Pontryagin difference. | [`MinkDiffScaledInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffScaledInner.lean) — Γ split into its two column blocks `Γₐ`, `Γᵦ`, the same matrix eq. (32a) concatenates | `correct` |

## Findings

**Algorithm 1 is now formalized, with its soundness; `Thm. 2` itself is formalized too, but only
under a hypothesis its own proof needs and never states — see the end of this section for why
that hypothesis, and not a weaker one, is what the row now links.** `ConZonotope.rowBound`, `tightenCoeff`,
`tightenRow` and `tighten`
([`Operations/`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/Tighten.lean)) are eq. 12
and the row-by-row pass exactly, and `ConZonotope.tighten_outer`
([`TightenOuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenOuter.lean))
is its soundness: every `β` with `Aβ = b` (every row) and `‖β‖∞ ≤ 1` (every coordinate) lands in
the box `tighten A b` returns. That is Algorithm 1's own guarantee, proved by
`Fin.foldl_induction` ([`Global/FoldInduction.lean`](../../src/CORALean/Global/FoldInduction.lean))
carrying it across the fold, and is worth having independent of `Thm. 2`.

`Thm. 2`'s own construction and equality proof turned out not to be separable from a second gap in
`tighten_outer` itself, found while attempting the `⊆` direction. That direction extends a point
`ξ` feasible for the *reduced* system (`Ar ξ = br` over `nc-1` rows, `ξ_c` dropped) back to a full
`ξ̃` feasible for `Zc`, by solving row `r` for `ξ̃_c` from the *other* coordinates. Bounding
`ξ̃_c ∈ [-1,1]` via `R_{r,c} ⊆ [-1,1]` needs those other coordinates in their own `E_k`, not merely
in `[-1,1]` — but `tighten_outer` only concludes `β_k ∈ E_k` from the *full* box hypothesis
`∀j, |β j| ≤ 1`, which includes `j = c`, the very coordinate not yet known to be bounded. Since
Algorithm 1's row-by-row updates are Gauss–Seidel, not Gauss–Jordan, a column's final `E_k` can
depend on every other column's running bound, `c` included, so this is not an artifact of how the
soundness proof was stated.

**The natural fix — a coordinate-`c`-free `tighten_outer`, sound at every column but `c` from the
*other* columns' boxes alone — is false in general, not merely unproved.** A 2-row, 2-column
witness (checked by running Algorithm 1's pass literally, not just argued): row 0 is
`ξ_0 + ξ_1 = 10.5`, row 1 is `ξ_0 - ξ_1 = -9.5`; the unique solution is `ξ_0 = 0.5`, `ξ_1 = 10`, so
`|ξ_0| ≤ 1` holds and only `ξ_1` (the coordinate to be excluded) is unbounded. Running the pass with
no hypothesis at `ξ_1`: row 0 tightens `E_0` to `[9.5, 1]` (already inverted, i.e. empty, since the
row-derived bound is clipped against the starting `[-1,1]`) and then `E_1` to `[1, 1]`; row 1 then
reads that corrupted `E_1 = [1,1]` to drive `E_0` down to `[9.5, -8.5]` — an interval that does not
contain the true `ξ_0 = 0.5` at all, even though `ξ_0` was bounded the whole time and its own rows
never carried a zero coefficient on `ξ_1`. (Row 1's own update to `E_1`, reading the now-corrupted
`E_0`, leaves it at `[1,1]` — unchanged, but already wrong, since the true `ξ_1 = 10` was excluded
from the very first row.) The corruption is real, not a proof artifact: Gauss–Seidel genuinely lets
an unbounded coordinate's row updates poison a *bounded* coordinate's, once the two share a row.

What does survive, proved here as `ConZonotope.tighten_outer_safe`
([`TightenOuterSafe.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenOuterSafe.lean)),
is soundness restricted to a set `S` of coordinates *closed* under "what a row reads when it
touches a coordinate of `S`": for every `j ∈ S` and row `i` with `a_{i,j} ≠ 0`, every other column
`l` that row reads (`a_{i,l} ≠ 0`) must also be in `S`. Given that closure, `Aβ = b` and
`|β j| ≤ 1` only for `j ∈ S`, every `k ∈ S` lands in `tighten`'s bound at `k` — no hypothesis at
all on the coordinates outside `S`. The witness above is exactly a case where no such `S` containing
column 0 but excluding column 1 exists (row 1 reads both with nonzero coefficient, so any `S`
containing 0 is forced to contain 1 too), which is why the unrestricted version fails there.

**The paper's own proof of `Thm. 2` (page 6 of the arXiv PDF) does not cross this point — it
asserts the `⊆` direction as a one-line consequence and never argues it.** After defining `Zr` via
`Λ_G`, `Λ_A`, it says only: "Through this transformation, the `r`th constraint is still imposed in
`Zr` but the ability to constrain `|ξ_c| ≤ 1` is lost. However, since `R_{r,c} ⊆ [-1,1]`, this
constraint is imposed by the remaining equality and norm constraints, and thus `Zr = Zc`." No
argument for *why* `R_{r,c}` (built from the final `E_k`, `k ≠ c`, of a full Algorithm 1 run on the
unreduced system) actually bounds `ξ̃_c` is given or cited at this step. Immediately after the proof,
the paper adds a procedural remark: "As in [18], Gauss-Jordan elimination with full pivoting should
be applied to `Zc` prior to applying Algorithm 1 to determine the intervals `Ek` required to compute
(12)." That is not part of `Thm. 2`'s stated hypotheses (only `a_{r,c} ≠ 0` and `R_{r,c} ⊆ [-1,1]`
are), and the paper never connects it back to the proof — but full pivoting is exactly the kind of
structural condition that could confine which columns a row's update depends on (a triangular
dependency has no cycle for corruption to run around), which is what the witness above shows is
otherwise needed. So this is a real gap in the paper, not only in this formalization: as literally
stated, `Thm. 2` is not established by its own proof.

**What closes it is naming the dependency-closure hypothesis directly, rather than forcing the
`⊆` direction through with something weaker.** `ConZonotope.eliminate`
([`Eliminate.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/Eliminate.lean)) is the
paper's construction — `Zr = {G−Λ_G A, c+Λ_G b, A−Λ_A A, b−Λ_A b}` via the rank-one `Λ_G`, `Λ_A` of
the proof, `CORALean.dropIdx`/`CORALean.sum_dropIdx`
([`DropIdx.lean`](../../src/CORALean/Global/DropIdx.lean)) dropping the zero row and column that
result in place of the paper's own "remove" step — and `ConZonotope.eliminate_exact_of_dependClosed`
([`EliminateExact.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/EliminateExact.lean))
is the full identity `Zc = Zr`, `⊇` by the routine algebra above (needing only `a_{r,c} ≠ 0`, not
`tighten_outer` at all) and `⊆` by exactly `tighten_outer_safe`'s `S`: the columns row `r` reads
besides `c`, `c` itself excluded, closed under what every row reads from `S`. Given that closure
and `R_{r,c} ⊆ [-1,1]`, `S`'s own soundness (`tighten_outer_safe`) plus one more sandwich at row
`r` (`aux_rowBound_dep`, the same argument `tightenCoeff`'s tightening step makes, run once
directly) bounds the eliminated coefficient itself — closing exactly the gap the witness above
demonstrates is real, and no more than it: `S` is a hypothesis of the theorem, not something
derived from full-pivoted Gauss-Jordan, which stays outside this pass.

`Global/DropIdx.lean` also gained `insertIdx` and `forall_dropIdx_iff`, `dropIdx`'s converse and
`sum_dropIdx`'s counterpart for a property rather than a sum — what extending the reduced system's
witness back to a full one, and stating the box and row-equation hypotheses over every index, both
needed.

**`Alg. 1 (R)` — `R` is computed from a tightened `E`.** The paper, repeating Scott et al.'s
eq. (A.1), says Algorithm 1 returns `R` with `R_j ⊃ {ξ_j | Aξ = b, |ξ_i| ≤ 1, ∀ i ≠ j}`, that is,
`R_j` should not use the bound `|ξ_j| ≤ 1` at all. Line 4 computes it from the running `E_k`,
and an earlier step may have tightened `E_k` with `|ξ_j| ≤ 1` in force. On the one row
`−2ξ₁ + ξ₂ = 0`, the step at `(1, 1)` gives `E₁ = [−½, ½]`, because `|ξ₂| ≤ 1`, and the step at
`(1, 2)` then gives `R₂ = 2E₁ = [−1, 1]`. Yet `ξ = (1, 2)` satisfies the row with `|ξ₁| ≤ 1`, and
`ξ₂ = 2 ∉ R₂`
([`TightenERNotSuperset.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenERNotSuperset.lean)).
This is the dependency `Thm. 2`'s proof runs into, above, seen from `R`. What `R` does contain is
`B∞(A, b)`'s projection: every feasible `ξ` with `‖ξ‖∞ ≤ 1` has `ξ_j ∈ E_j` and `ξ_j ∈ R_j`, after
any number of passes
([`TightenEROuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenEROuter.lean)).
That is all the emptiness test `E ∩ R = ∅ ⇒ Z_c = ∅` uses, so the test is sound as printed
([`TightenEREmpty.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenEREmpty.lean)).
