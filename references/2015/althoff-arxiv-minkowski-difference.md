# On Computing the Minkowski Difference of Zonotopes

M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv, 2015.

**Source:** https://arxiv.org/pdf/1512.02794 (read as the PDF; its numbering agrees
exactly with the ar5iv rendering at https://ar5iv.labs.arxiv.org/html/1512.02794
this page was first read from — all seventeen locators checked against the PDF
text, Def. 1 through Prop. 6, and none differ)  
**Inventory:** confirmed

The Minkowski difference of zonotopes: exact where the generators align, and
approximated otherwise. `minkDiffAligned` is the exact case; CORA's default
`'approx'` is not followed here — see [FINDINGS.md](../../FINDINGS.md).

**What closed the last three rows.** The gate all three shared is open: `Thm. 2` is proved at every zonotope whose
generators span, in
[`HRepEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HRepEq.lean),
and `Lemma 2` reads off it. The exhaustion — that the 2·C(p,n−1) cross-product
normals cover every facet — is a cone argument rather than a facet enumeration:
a point outside the zonotope has a separating direction; the generators signed
by that direction make it a point of a pointed cone on which the separation is a
positive linear form;
[`ConeEdge.lean`](../../src/CORALean/Global/ConeEdge.lean) walks it to an edge
of that cone, which n independent generators annihilate; and
[`EqSmulNCross.lean`](../../src/CORALean/Global/EqSmulNCross.lean) says an edge
is a multiple of their cross product. Mathlib has no polytope, facet or
extreme-ray theory to do this with, so the walk is written out here.

Each of the three then wanted one thing more. `Prop. 1` wanted Fig. 6's
numbers; they are in the printed proof and are used verbatim, and the plot the
proof reads its conclusion off is replaced by a named face. `Prop. 6` wanted
(22) solved, and (22) solved exactly is precisely where `Thm. 4`'s inequality
and `Thm. 5`'s meet, so the exactness follows from the two rows already here —
with µ ≥ 0, which the printed statement omits and is false without, and with
unique solvability, which is what (23) asserts for n = 2 and is the row's named
side condition.

`Prop. 2` comes in two halves, and the earlier verdict that a linear program
blocks it was only half right. The program picks the redundant set; *given* that
set the printed criterion is pure counting, and that counting is
[`GenRemovableIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenRemovableIff.lean),
which equates the printed sum with "every halfspace this generator spans is
redundant". The other half, from there to "the generator is no longer required",
is one sentence of the printed proof and is
[`GenNotRequiredIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenNotRequiredIff.lean);
it needs the *minimum* H-representation, which is a hypothesis there and a theorem in
[`GenNotRequiredIffOfFullDim.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenNotRequiredIffOfFullDim.lean)
for a full-dimensional difference whose rows cut distinct halfspaces — see the findings below.

`Thm. 4` and `Thm. 5` ask for the halfspace description as an explicit
hypothesis, which is exactly what their own printed proofs take from `Thm. 2`;
[`HRepLinSubset.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HRepLinSubset.lean)
discharges it at `Thm. 2`'s own normals.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotope, G-Representation) Z = {c + Σ β_i g^(i) \| β_i∈[-1,1]}, order ϱ=p/n; shorthand Z=(c,g^(1),...,g^(p)). | n/a — restated from A. Girard, "Reachability of Uncertain Linear Systems Using Zonotopes", HSCC 2005, where the representation is introduced | `restated` |
| `Lemma 1` | (Minkowski Difference from Finitely Many Intersections) [cites [37, Thm 2.1]] For convex subtrahend Z_s, Z_m ⊖ Z_s = ⋂_{v^(i)∈V} (Z_m - v^(i)) over the vertices V of Z_s. | [`MinkowskiDiffEqIInter.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffEqIInter.lean) — at any `V` whose convex hull covers `Z_s`, the paper's vertex set being one such `V`, and nothing here needs `V` finite. Convexity is asked of the **minuend**, not, as printed, of the subtrahend: the hull argument runs on `{z \| x + z ∈ Z_m}`, and `Z_s` convex is neither used nor implied | `underspecified` — convexity is printed for the subtrahend; the argument needs it of the minuend |
| `Thm. 1` | (Minkowski Difference from Generators) For zonotopes Z_m, Z_s, Z_m ⊖ Z_s can be computed by a recursive procedure using only the generators of Z_s: Z_int^(1) = Z_m - c^(s), Z_int^(i+1) = (Z_int^(i)+g^(s,i)) ∩ (Z_int^(i)-g^(s,i)), giving Z_m⊖Z_s = Z_int^(p_s+1). | [`MinkDiffGenRecExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffGenRecExact.lean) | `proof-gap` — eq. (8) is false for non-convex sets; the theorem holds since every set the recursion reaches is convex |
| `Def. 2` | (n-dimensional cross product) [cites [47]] For n-1 vectors h^(i) stored in H, nX(H) = [det(H^[1]), -det(H^[2]), ..., (-1)^{n+1}det(H^[n])]^T, where H^[i] is H with row i removed. | [`CrossProduct.lean`](../../src/CORALean/Global/CrossProduct.lean) — at `Mat ℝ (n+1) n`, the printed `Mat ℝ n (n-1)` with the ambient dimension named as a successor so that dropping a row needs no truncated subtraction; the printed sign `(-1)^{i+1}` counts rows from one and is `(-1)^i` at a zero-based index. The same file proves what makes it a normal vector, `nX(H)` annihilating every column of `H` | `correct` |
| `Thm. 2` | (H-Representation of Zonotopes) [cites [10, Thm. 7]] Gives the halfspace representation Cx≤d of a zonotope (c,G) with p independent generators, using the normalized cross products nX of combinations of generators for C, and Δd = Σ\|C+g^(υ)\| for the offset. | [`HRepEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HRepEq.lean), the rows themselves [`FacetNormal.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/FacetNormal.lean) — an equality, at every zonotope in ℝ^(n+1) whose generators span it, which is what "p independent generators" asks for. Three departures. The rows are indexed by *every* selection `Fin n → Fin p` rather than by the C(p,n−1) subsets: a repeated index makes nX zero and the row vacuous, and two orderings of one subset differ by a sign, so the family is the printed 2·C(p,n−1) rows and nothing else. The normalization is dropped — a halfspace is unchanged by scaling its normal and its offset together, and Δd scales with C. And the ± pair is written as one \|·\| row rather than two. **As printed:** each departure denotes the same halfspace set — the printed rows are among the selections and every other selection is vacuous or repeats one up to sign, a positive scaling of a normal and its offset leaves its halfspace unchanged, and `\|r\| ≤ Δd` is the pair `±r ≤ Δd` — so the equality proved is the printed `Z = {x \| Cx ≤ d}` | `correct` |
| `Lemma 2` | (H-Representation of Intersection of Translated Zonotopes) For Z_o=(c-h,G) and Z_t=(c+h,G), the halfspace representation of Z_o∩Z_t has the same C matrix as Thm. 2 but a d vector adjusted by Δd_trans = \|C+h\|. | [`HRepInterEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HRepInterEq.lean) — an equality, under `Thm. 2`'s own spanning hypothesis and at its rows, `Z_o` and `Z_t` written with `Zonotope.shift`, whose sign convention makes them `Z.shift h` and `Z.shift (-h)` | `correct` |
| `Thm. 3` | (H-Representation of the Minkowski Difference) For zonotopes Z_m=(c^(m),G^(m)) and Z_s=(c^(s),G^(s)), gives the halfspace representation Cx≤d of Z_m⊖Z_s, with the same C matrix as Thm. 2 and d adjusted by both Δd and Δd_trans. | [`MinkowskiDiffHRepEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkowskiDiffHRepEq.lean) — an equality, at `Thm. 2`'s own hypothesis on `Z_m` alone (its generators span) and none on `Z_s`, and at `Thm. 2`'s own `±`-as-one-`\|·\|`-row convention. The enclosing half reads `MinkowskiDiffApplyLe.lean` at a direction and its negation; the exhausting half reads `Z_m`'s own halfspace description, `HRepEq.lean`, at the point the subtrahend displaces. `minkDiff` is still not computed this way — CORA's `'approx'` scales the minuend's generators by a pseudoinverse solution nothing checks, so it is computed from a checked generator representation instead; see `Zonotope Minkowski difference` in [FINDINGS.md](../../FINDINGS.md). The identity is also proved at the `Bool × Finset (Fin Zm.h)` rows `Prop. 2` counts over, [`MinkowskiDiffRowsEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkowskiDiffRowsEq.lean), which is what discharges `gen_not_required_iff`'s `hrows`; see the findings below | `correct` |
| `Prop. 1` | (Zonotopes are not closed under Minkowski difference) Gives an explicit 3D counterexample zonotope pair Z_m, Z_s for which Z_m⊖Z_s is not itself a zonotope. | [`MinkowskiDiffNotZonotope.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkowskiDiffNotZonotope.lean) — the paper's own pair, G⁽ᵐ⁾ = [[1,1,0,0],[1,0,1,0],[1,0,0,1]] and G⁽ˢ⁾ = G⁽ᵐ⁾/3 with the first column's first entry negated, both centred at the origin. One departure, in the proof and not in the statement: the printed proof is a plot ("as one can see in the plot of Z_m⊖Z_s in Fig. 6"), and a plot proves nothing here, so the face it points at is named instead. The difference lies under x₂ ≤ 4/3, x₂ − x₁ ≤ 2/3, x₁ − x₃ ≤ 2/3 and x₃ ≤ 4/3, and (2/3, 4/3, 0), (2/3, 4/3, 4/3) and (4/3, 4/3, 4/3) all sit on x₂ = 4/3; no centre reflects all three back into it. That a zonotope has no such face is [`FaceCentrallySymmetric.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FaceCentrallySymmetric.lean) | `correct` |
| `Prop. 2` | (Generator removal) Gives a necessary-and-sufficient combinatorial condition (a sum of indicator terms equal to 2·C(p_m-1,n-2)) for the i-th generator of the minuend Z_m to be droppable without affecting Z_m⊖Z_s. | [`GenNotRequiredIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenNotRequiredIff.lean), the counting identity underneath it [`GenRemovableIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenRemovableIff.lean) — the printed biconditional, with "no longer required for the difference" read as the printed proof reads it: the difference is still cut out by the rows of `C` that g⁽ᵐ˒ⁱ⁾ does not span. Two departures, and one hypothesis discharged. Which halfspaces are redundant stays a parameter, as `Sec. 4.1` leaves it — obtained by linear programming, and nothing here computes it. `Thm. 3`'s identity is a hypothesis of `gen_not_required_iff` itself, `hrows`, but a theorem at `Thm. 3`'s own rows: `gen_not_required_iff_of_span` ([`GenNotRequiredIffOfSpan.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenNotRequiredIffOfSpan.lean)) is the same biconditional with `hrows` discharged by `minkowskiDiff_rows_eq`, at `Thm. 2`'s hypothesis that the minuend's generators span — see the findings below. The **minimum** H-representation is a hypothesis, in the form that says exactly that: dropping every redundant row still describes the difference, and no row outside the redundant set is redundant. That is what carries the printed proof's one-sentence step — each row being redundant on its own would not. Both halves are theorems at `Thm. 3`'s rows when the difference has nonempty interior and no two rows cut the same proper halfspace: `gen_not_required_iff_of_fullDim` ([`GenNotRequiredIffOfFullDim.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenNotRequiredIffOfFullDim.lean)) takes the redundant set to be the rows the others imply, and `rows_eq_drop_redundant` ([`RowsEqDropRedundant.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/RowsEqDropRedundant.lean)) proves that dropping all of them at once leaves the difference; see the findings below. | `underspecified` — needs a full-dimensional difference and rows cutting distinct halfspaces, neither printed |
| `Prop. 2 (complexity)` | Checking the condition for all generators has computational complexity O(C(p_m,n-1)·p_m²) with respect to the dimension n. | n/a — a running time stated of the construction, which the tree can only assert (`Complexity/Time/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Thm. 4` | (Under-Approximative G-Representation of the Minkowski Difference) Gives an under-approximating generator representation (ĉ,Ĝ) of Z_m⊖Z_s, with ĉ=c^(m)-c^(s) and Ĝ=Ĝ^(m)μ*, μ* the solution of an LP maximizing ζ^Tμ subject to Âμ≤b̂, μ≥0. | [`MinkDiffStretchInnerHRep.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffStretchInnerHRep.lean) — the theorem at `Thm. 2`'s own directions, the cross products of a minuend whose generators span, both signs: the stretched minuend at any `µ ≥ 0` feasible for `Âµ ≤ b̂` lies in `Z_m ⊖ Z_s`, the linear program's optimum `µ*` among them; [`MinkDiffStretchInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffStretchInner.lean), the representation itself [`MinkDiffStretch.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/MinkDiffStretch.lean) — the same at any directions describing the minuend, inner, as `MinkDiff` obliges: `μ` is any point feasible for `Âμ ≤ b̂`, not (15)'s optimum: `ζ` is "a user-specified vector" and the objective picks among feasible `μ` without carrying the guarantee, so an optimum is a tightening and not a soundness condition, and that the directions `C` *describe* the minuend, which the printed proof reads off `Thm. 2`, is a hypothesis; [`HRepLinSubset.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HRepLinSubset.lean) discharges it at those rows, and `C` is indexed by a type, not a `Fin q`, so that their own index serves. `Ĝ^(m)` is `G^(m)` with no generator removal, which is what the paper's own HC-u runs | `correct` |
| `Thm. 5` | (Over-Approximative G-Representation of the Minkowski Difference) Gives an over-approximating generator representation (c̃,G̃) analogous to Thm. 4, with μ* solving a differently-signed LP (minimizing ζ^Tμ subject to -Âμ≤-b̃, μ≥0). | [`MinkDiffStretchOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffStretchOuter.lean) over the same [`MinkDiffStretch.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/MinkDiffStretch.lean) — outer, and recorded only here: `Thm. 4`'s row is the inner one and neither stands in for the other. `b̃` is a parameter with the one property (18) is wanted for, that it bounds the exact difference in each direction; [`MinkowskiDiffApplyLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkowskiDiffApplyLe.lean) proves `Δd - Δd_trans` is such a `b̃` — the most conservative admissible one, which is why (18) may lower it. Same `Thm. 2` premise as `Thm. 4`, read at the stretched minuend, and discharged the same way — `hRep_lin_subset` allows a positive rescaling of each normal, which is what stretching by `µ` does to them | `correct` |
| `Prop. 3` | For C⊆A, {a+b \| a⊕C⊆A, b∈B} ⊆ {a+b \| a+b⊕C⊆A⊕B} — a general set-enclosure monotonicity lemma used in later proofs about combining Minkowski differences and sums. | [`MinkowskiDiffAddSubsetAdd.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffAddSubsetAdd.lean) — the inclusion with no hypothesis, since neither the paper's proof nor ours uses `C ⊆ A`; [`MinkowskiDiffAddSubsetAddOfSubset.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffAddSubsetAddOfSubset.lean) — the printed statement, hypothesis `C ⊆ A` included, read off it | `correct` |
| `Prop. 4` | For Z_{m,encl}⊇Z_s, (Z_{m,encl}⊖Z_s)⊕Z_{m,rem} ⊆ (Z_{m,encl}⊕Z_{m,rem})⊖Z_s — a distributivity-type inclusion relating Minkowski difference/sum when the minuend is split into an enclosing part and a remainder. | [`MinkowskiDiffEnclSubsetAdd.lean`](../../src/CORALean/ContSet/ContSet/Theorems/MinkowskiDiffEnclSubsetAdd.lean) | `correct` |
| `Alg. 1` | (Generator Selection for Z_m) Sorts the generators of Z_m by length and greedily adds them, comparing interval-hull (box) ratios against Z_s, to build an enclosing Z_{m,encl}⊇Z_s with as few generators as possible; used by Prop. 4. | [`EnclGenSel.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/EnclGenSel.lean) — all fourteen lines, one `let` per printed step, over [`GenSelection.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/GenSelection.lean)'s `(c, g_sort^(1..ξ))`. Three departures, all in the findings below: lines 6 and 9 are one cross-multiplied test because line 4's `µ ← inf` is no real number, `sort` ranks by the squared length rather than `‖·‖₂`, and line 11's containment test is the caller's `encloses`. What holds whatever that oracle answers is [`EnclGenSelSubset.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/EnclGenSelSubset.lean), `Z_{m,encl} ⊆ Z_m` — the enclosure `Z_{m,encl} ⊇ Z_s` is the oracle's claim and is not proved here | `underspecified` — line 11 loop test is printed the wrong way round; line 4 `µ ← inf` is no real number |
| `Def. 3` | (Aligned zonotopes) Two zonotopes Z1=(c,g^(1),...,g^(p1)), Z2=(d,h^(1),...,h^(p2)) (each with no internally-aligned generators): Z1 is aligned with Z2 if every generator of Z2 is parallel (up to scaling) to some generator of Z1; if that holds both ways, the zonotopes are mutually aligned. | [`Aligned.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/Aligned.lean) — `AlignedWith`, `MutuallyAligned`, and the standing "no internally-aligned generators" assumption as `NoAlignedGens`, which is a normalization of each operand and so is not a hypothesis of the relation. The scaling γ is unconstrained, exactly as printed; that `minkDiffAligned`'s index-for-index pairing is a witness for it is [`AlignedWithOfSmul.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/AlignedWithOfSmul.lean) | `correct` |
| `Prop. 5` | (Minkowski difference for aligned generators) If Z_m is aligned with Z_s (γ_i g^(m,i) = g^(s,i) for i=1..p_s after reordering), then Z_m⊖Z_s is computed exactly as (c^(m)-c^(s), g^(m,1)-g^(s,1), ..., g^(m,ps)-g^(s,ps), g^(m,ps+1), ..., g^(m,pm)). | [`MinkDiffAlignedExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffAlignedExact.lean), the closed form itself [`MinkDiffAligned.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/MinkDiffAligned.lean) — proved with the alignment factor confined to `0 ≤ γ_i ≤ 1`, which the printed statement does not ask for and is false without (see the findings below), and at equal generator counts (`Z₁.h = Z₂.h`; the printed statement allows `p_s ≤ p_m`, padding `Z_s` with zero generators — `μ = 0` is allowed — recovers it); [`MinkDiffAlignedNotInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffAlignedNotInner.lean) — the one-generator counterexample outside `[0, 1]` **Counterexample:** `Zonotope.minkDiffAligned_not_inner` | `fixed` — false for alignment factors outside `[0,1]` (one generator in ℝ); formalized with `0 ≤ γᵢ ≤ 1` |
| `Prop. 6` | (Minkowski difference of two-dimensional zonotopes) Gives a closed-form zonotope (c^(m)-c^(s), Ĝ^(m)\|Ĉ+Ĝ^(m)\|^{-1}(Δd̂-Δd̂_trans)) for the Minkowski difference of two 2-dimensional zonotopes (exact, since the 2D case is always aligned/tractable). | [`MinkDiffStretchEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffStretchEq.lean) over the same [`MinkDiffStretch.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/MinkDiffStretch.lean) — the **identity**, not an enclosure either way, which is what "exact" asks for. The closed form is read off (22), \|Ĉ⁺Ĝ⁽ᵐ⁾\|µ = Δd̂ − Δd̂_trans, and (22) solved exactly is where `Thm. 4`'s constraint and `Thm. 5`'s meet, so the two rows above give the two inclusions at one µ. Two side conditions. µ is an argument satisfying (22), not a matrix inverse: that (22) is uniquely solvable is what (23) asserts for n = 2 and nothing here proves it. And µ ≥ 0 is required and is not printed — see the findings below; [`MinkDiffStretchEqCounterexample.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffStretchEqCounterexample.lean) — (22) solved at `µ = -1` in one dimension, where the closed form is not the (empty) difference **Counterexample:** `Zonotope.minkDiffStretch_eq_counterexample` | `fixed` — false without `µ ≥ 0` (explicit pair in ℝ²); (23)'s normal is printed with the wrong sign |

## Findings

**`Thm. 1` — eq. (8) is stated for a set, and is false off the convex ones.** The proof's
eq. (8), `A ⊖ ([-1,1] ⊗ g) = (A + g) ∩ (A − g)`, is asserted "for a set `A`". At
`A = {-1, 1} ⊆ ℝ` with `g = 1` the left side is `∅` and the right is `{0}`. The theorem
itself is untouched: every set the recursion reaches is convex, since it starts at a
zonotope and translates and intersections of convex sets stay convex. So the claim holds
and needs no extra hypothesis — convexity is carried along the induction here rather than
assumed.
[`MinkDiffGenRecExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffGenRecExact.lean)

**`Prop. 5` — the alignment factor is unconstrained, and the closed form is false
outside `[0, 1]`.** `Def. 3` lets `γ_i` be any real and `Prop. 5` inherits it. One
generator in ℝ refutes the printed statement: at `Z_m = (0, 1)` and `Z_s = (0, γ)` the
form `(0, 1 - γ)` holds the point `1 - γ`, which `-γ ∈ Z_s` carries out of `Z_m` to
`1 - 2γ` whenever `γ < 0` or `γ > 1`. So it is not the difference, nor even contained in
it: at `γ > 1` the difference is empty while the form is not, and at `γ < 0` the
subtrahend is the same set it is at `-γ` while the form lengthens the generator instead
of shortening it. Formalized with `0 ≤ γ_i ≤ 1`, which is exactly where the paper's own
`(Z_m ⊖ Z_s) ⊕ Z_s = Z_m` step holds, `|1 - γ_i| + |γ_i|` being `1` there and more
elsewhere.
[`MinkDiffAlignedNotInner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffAlignedNotInner.lean)

**`Alg. 1` — line 4's `µ ← inf` is not a real number, and line 11's test is printed the
wrong way round.** Two transcription departures, neither optional. Line 4 initializes `µ`
to infinity precisely because line 2 sets `r_sel = 0` and line 9's `maxᵢ r_{s,i}/r_{sel,i}`
is then a division by zero; over ℝ, `0/0 = 0`, which would stop the loop at once instead of
entering it. Lines 6 and 9 are therefore one cross-multiplied test, `µ̄ · r_{sel,i} <
r_{s,i}`, which is total, agrees with the ratio wherever the ratio is defined, and reads
`r_sel = 0` as the intended infinity. Line 11 as printed loops `while Z_s ⊃ (c_s,
g_sort^(1..ξ))` — while the *subtrahend* strictly contains the selection — and leaving on
the negation of that gives `Z_s ⊉ selection`, which is not the enclosure the line exists to
establish. The prose above the listing says what is meant: "Afterwards, more generators are
added in case Z_{m,encl} ⊉ Z_s". That is what is transcribed. The sort key is a third,
harmless one: generators are ranked by `∑ₖ gₖ²` rather than `‖·‖₂`, the same order without
a square root.
[`EnclGenSel.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/EnclGenSel.lean)

**`Prop. 6` — the closed form needs µ ≥ 0, and (23)'s normal has the wrong
sign.** A zonotope generator may be negated without changing the set, so the
reach of the stretched minuend in the direction Ĉ⁺ᵢ is Σⱼ \|Ĉ⁺ᵢĝ⁽ʲ⁾\|·\|µⱼ\|,
not Σⱼ \|Ĉ⁺ᵢĝ⁽ʲ⁾\|µⱼ. Where the solution of (22) has a negative entry the two
differ and the closed form is not the difference. One pair in ℝ² settles it:
Z_m = (0, e₁, e₂), the square [−1,1]², and Z_s = (0, 2e₁, 2e₂), twice it. The
difference is empty. `Def. 2`'s normals are (0,−1) and (1,0), so Â = [[0,1],
[1,0]] and Δd̂ − Δd̂_trans = (1 − 2, 1 − 2); (22) has the unique solution
µ = (−1, −1), and the closed form (0, −e₁, −e₂) is the minuend back again.
So `minkDiffStretch_eq` carries µ ≥ 0, which the printed proposition does not.
The second departure is a transcription slip in the source: (23) prints
C⁺ᵢ = [g⁽ⁱ⁾₂ g⁽ⁱ⁾₁]/‖·‖₂, which is not orthogonal to g⁽ⁱ⁾; `Def. 2`'s own nX at
n = 2 gives [g⁽ⁱ⁾₂, −g⁽ⁱ⁾₁], which is. Nothing downstream turns on it — the
row's statement is at an abstract family of directions — but the printed matrix
is not the normal it is called.
[`MinkDiffStretchEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkDiffStretchEq.lean)

**`Thm. 3` — proved at both index families, so `gen_not_required_iff`'s `hrows` is
a theorem.**
[`MinkowskiDiffHRepEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkowskiDiffHRepEq.lean),
`Zonotope.minkowskiDiff_hRep_eq`, is the identity itself: `Z_m ⊖ Z_s = {x \| C(x −
(c⁽ᵐ⁾ − c⁽ˢ⁾)) ≤ Δd − Δd_trans}`, `C` `Thm. 2`'s own cross-product normals at
`Z_m` and Δd_trans the subtrahend's own reach in each direction. It needs only
`Thm. 2`'s own hypothesis, that `Z_m`'s generators span — nothing about `Z_s` —
and it reads `± → one \|·\| row` exactly as `HRepEq.lean`/`HRepInterEq.lean`
already do: one row per selection `S : Fin (n+1) → Fin Z_m.h`, `Thm. 2`'s own
indexing, not the printed `C(p,n−1)` subsets. `GenRemovableIff.lean` and
`GenNotRequiredIff.lean` use the other encoding for the same family — `Bool ×
Finset (Fin Zm.h)`, one row per signed generator subset.
[`MinkowskiDiffRowsEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MinkowskiDiffRowsEq.lean),
`Zonotope.minkowskiDiff_rows_eq`, bridges the two: the rows are
`Zonotope.minkDiffRowNormal` (`±` the cross product of the subset's generators in
increasing order) and `Zonotope.minkDiffRowOffset`. A selection with a repeated
generator has normal `0` (`FacetNormalEqZeroOfNotInjective.lean`) and its row
is `0 ≤ 0`; an injective one is a reordering of its image's increasing selection,
which changes the normal by the permutation's sign
(`FacetNormalCompPermAbs.lean`, through `Matrix.det_permute'`), so
`\|·\|` is unchanged; and the `true`/`false` rows of a subset are the two sides
of that `\|·\|`. `GenNotRequiredIffOfSpan.lean` is `gen_not_required_iff` at
those rows with `hrows` discharged; the original, at free `C`/`d`, stays beside
it. The minimum-H-representation hypotheses `hmin`/`hirr` are discharged in
`GenNotRequiredIffOfFullDim.lean`, below.

**`Prop. 2` — the minimum H-representation needs two hypotheses the paper does
not print.** The printed biconditional is "the i-th
generator is no longer required for the difference ⟺ ∑ⱼ ind⁽ʲ⁾ᵢ = 2·C(p_m−1, n−2)",
and its proof runs through a middle term: each generator spans exactly
2·C(p_m−1, n−2) facets, so the sum over the redundant halfspaces hits that
number exactly when all of them are redundant. That equivalence is
[`GenRemovableIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenRemovableIff.lean),
and it is combinatorics with no linear program in it. The step from there to
"the generator is no longer required" is
[`GenNotRequiredIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenNotRequiredIff.lean),
which reads that phrase as the printed proof does — the halfspaces the generator
does not span still describe the difference — and takes the minimum
H-representation as a hypothesis, in the two-part form that pins it down: every
row outside the redundant set is irredundant, and dropping the redundant ones
all at once still describes the difference. The second part is what does the
work, and it does not follow from the first: two rows cutting the same halfspace
are each redundant on its own and jointly are not. What would discharge it is
the classical fact that a full-dimensional polytope whose description has no two
rows cutting the same halfspace is already described by its irredundant
halfspaces. That fact is
[`RowsEqDropRedundant.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/RowsEqDropRedundant.lean),
`rows_eq_drop_redundant`, proved without facets: two redundant rows `j ≠ k` and a
point `y` breaking both and nothing else; from an interior point `z` the segment
to `y` crosses row `i` at `pᵢ/(pᵢ + qᵢ)` (slack at `z`, excess at `y`), and the
two crossings coincide only on the affine set `p_j q_k = p_k q_j` in `z`, which
fills the open interior only if the rows are proportional. So some `z` crosses
one first, and a point between the crossings breaks that row alone — it was not
redundant. Dropping the rows one at a time is then an induction.
[`GenNotRequiredIffOfFullDim.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GenNotRequiredIffOfFullDim.lean)
is `Prop. 2` with the redundant set computed as the rows the others imply and
both hypotheses discharged. Neither hypothesis of the fact is printed: `Prop. 2`
says nothing about Z_m ⊖ Z_s being full-dimensional, and it need not be — the
difference may be lower-dimensional or empty, and then the minimum
H-representation is not unique and the criterion is not about anything — nor
about the rows cutting distinct halfspaces, which for `Thm. 2`'s rows is the
minuend's generators in general position; with one halfspace cut twice, both
copies are redundant and the printed count can call a generator droppable that
is not.
