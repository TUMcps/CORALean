# On the co-NP-Completeness of the Zonotope Containment Problem

```bibtex
@article{kulmburg2021co,
  author = {Kulmburg, A. and Althoff, M.},
  title = {On the co-NP-Completeness of the Zonotope Containment Problem},
  journal = {European Journal of Control},
  year = {2021}
}
```

**In the paper's bibliography.**

**Source:** https://mediatum.ub.tum.de/doc/1616344/document.pdf (the accepted manuscript on TUM's repository, "Preprint submitted to European Journal of Control April 20, 2021", 12 pages, read in full; text extracted with `pypdf`). The typeset Elsevier article (doi:10.1016/j.ejcon.2021.06.028) was not reachable; numbering is the manuscript's, which is the one CORA cites (`Definition 4`, `Algorithm 1`, `Algorithm 2`).  
**Inventory:** confirmed (against the manuscript: Definitions 1-4, Lemmas 1-6, Theorems 1-2, Corollaries 1-4, Remarks 1-2 and Algorithms 1-2, each with its own counter; the equations below are the numbered displays that make a claim)

The zonotope norm `‖p‖_Z = min {‖γ‖∞ | G γ = p}`, CORA's `zonotopeNorm`, and with it the
containment problem `Z₁ ⊆ Z₂` as the maximization of a convex function over `Z₁`, which the
paper proves co-NP-complete by reducing the circumradius of a parallelotope to the inradius
of a zonotope. The norm, its properties and the two exact algorithms CORA runs as
`contains_(..., 'exact:venum')` and `'exact:polymax'` are formalized, as are the reduction's
lemmas, the geometric `Lemma 6` included; the hardness theorem and its corollary are not, the
tree having no complexity classes to state NP-hardness or co-NP-completeness in. Two
equations of the reduction and `Lemma 1`'s unit-ball claim are false as printed, and
`Remark 2` is false.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | A polytope in H-representation {Hx ≤ h} or V-representation conv(v₁, …, v_k), the two equivalent. | n/a — the textbook representations and their equivalence (Minkowski-Weyl), restated from Ziegler | `restated` |
| `Def. 2` | A zonotope ⟨c, G⟩ = {c + Gβ \| β ∈ [-1, 1]^m}; it has at most 2(m choose n-1) facets, a tight bound. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md); the facet count is cited from Althoff et al. 2010 | `restated` |
| `Def. 3` | (Polyhedral asymmetric norm) For a bounded polytope {ηᵢᵀx ≤ hᵢ} with every hᵢ ≠ 0, S_P(x) = max{0, η₁ᵀx/h₁, …, η_sᵀx/h_s}. | [`PolyNorm.lean`](../../src/CORALean/ContSet/HPolytope/Real/Definitions/PolyNorm.lean) | `correct` |
| `Lemma 1` | S_P is an asymmetric norm (triangle inequality, positive homogeneity); if symmetric it is a norm; its unit ball is P. | [`PolyNormIsAsymmNorm.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/PolyNormIsAsymmNorm.lean), [`PolyNormIsAsymmNorm.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/PolyNormIsAsymmNorm.lean) — the first two at any h, the last two at every hᵢ > 0, and the counterexample to the unit ball at hᵢ ≠ 0 **Counterexample:** `HPolytope.polyNorm_isAsymmNorm_counterexample` | `fixed` — the unit ball is P only with the origin inside (every hᵢ > 0): P = [1, 2] has hᵢ ≠ 0 and S_P(0) = 0; true with hᵢ > 0; see Findings |
| `Lemma 2` | For Z = ⟨0, G⟩, m ≥ n: G has rank n ⇔ Z has an interior ⇔ G is surjective ⇔ ν is defined everywhere and positive definite. | [`ZonotopeNormTFAE.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ZonotopeNormTFAE.lean) — each against "onto", at any center and without m ≥ n | `correct` |
| `Thm. 1` | For G ∈ ℝ^{n×m} of rank n, ν(p) = min {‖γ‖∞ \| Gγ = p} is a norm on ℝⁿ. | [`ZonotopeNormIsNorm.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ZonotopeNormIsNorm.lean), [`CoeffNorm.lean`](../../src/CORALean/Global/CoeffNorm.lean) — rank n read as onto (`Lemma 2`); over any real module | `correct` |
| `Def. 4` | (Z-norm) ‖p‖_Z := ν(p) for the translate ⟨0, G⟩ of a non-degenerate Z. | [`ZonotopeNorm.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/ZonotopeNorm.lean) — CORA's `zonotopeNorm`; `0` where no γ reaches p, which the paper does not define | `correct` |
| `Cor. 1` | For non-degenerate Z = ⟨c, G⟩: B^Z_1(c) = Z and C^Z_1(c) = ∂Z. | [`ZonotopeNormBallEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ZonotopeNormBallEq.lean) | `correct` |
| `Remark 1` | G(∂[-1, 1]^m) ⊇ C^Z_1(0) always holds, while the converse is not necessarily true. | [`ZonotopeNormSphereSubsetImage.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ZonotopeNormSphereSubsetImage.lean) — both: the inclusion, and G = (1, 1), (1, 0) ↦ 1 with ‖1‖_Z = 1/2 | `correct` |
| `Cor. 2` | For non-degenerate Z centered at the origin, ‖p‖_Z = S_Z(p). | [`ZonotopeNormEqPolyNorm.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ZonotopeNormEqPolyNorm.lean) — for any halfspace representation of Z with every hᵢ ≠ 0, which forces hᵢ > 0 | `correct` |
| `Remark 2` | For degenerate Z `Cor. 2` fails, ‖·‖_Z not being defined everywhere; "however, even in that case, S_Z is a norm, and can be used instead of ‖·‖_Z to check whether a point lies in Z". | [`NotExistsPolyNormOfDegenerate.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/NotExistsPolyNormOfDegenerate.lean) — a degenerate Z centered at the origin has no halfspace representation with every hᵢ ≠ 0, so S_Z does not exist | `false` — S_Z needs every hᵢ ≠ 0 (`Def. 3`), and a degenerate Z centered at 0 admits no such representation (it would contain an open set around 0); no norm has it as unit ball; see Findings |
| `Cor. 3` | For non-degenerate Z, ‖·‖_Z is equivalent to all p-norms, convex, Lipschitz-continuous and differentiable almost everywhere. | [`ZonotopeNormEquivNorm.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ZonotopeNormEquivNorm.lean) — equivalence against the supremum norm; almost everywhere by Rademacher's theorem | `correct` |
| `Eq. 18` | (ZC) Z₁ ⊆ Z₂ iff ‖p - c₂‖_{Z₂} ≤ 1 for every p ∈ Z₁. | [`SubsetIffZonotopeNormLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SubsetIffZonotopeNormLe.lean) — Z₂ non-degenerate | `correct` |
| `Eq. 20` | r∞(Z) = 1/d(c + [-1, -1]ⁿ, Z), the inradius against the containment radius d of Eq. 19. | [`InradiusEqInvContainmentRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/InradiusEqInvContainmentRadius.lean) — the cube [-1, 1]ⁿ, Z non-degenerate, n > 0; the maximum d attained | `underspecified` — the cube is misprinted [-1, -1]ⁿ, and n > 0 is needed (at n = 0, d = 0 and every cube fits) |
| `Lemma 3` | For H = {bᵀx ≤ 1} ∋ 0, the largest cube r[-1, 1]ⁿ inside H has r = 1/‖b‖₁. | [`CubeSubsetHalfspaceIff.lean`](../../src/CORALean/Global/CubeSubsetHalfspaceIff.lean) — the cube fits iff r‖b‖₁ ≤ 1, and the greatest radius at b ≠ 0 | `underspecified` — b ≠ 0 is missing: at b = 0, H = ℝⁿ and no cube is largest |
| `Lemma 4` | For P bounded, non-degenerate and centrally symmetric, R₁(P) = 1/r∞(P^Δ). | [`L1CircumradiusEqInvInradiusPolar.lean`](../../src/CORALean/Global/L1CircumradiusEqInvInradiusPolar.lean) — P = conv(v₁, …, v_N) with a nonzero vᵢ; P^Δ the polar {x \| yᵀx ≤ 1 ∀ y ∈ P}; symmetry not needed | `correct` |
| `Eq. 29` | Π = Σᵢ [-1, 1]zᵢ = {x \| Vx ≤ 1}, V the rows ±zᵢ. | [`ParallelotopeEqAbsMulVecLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/ParallelotopeEqAbsMulVecLe.lean), [`ParallelotopeEqAbsMulVecLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ParallelotopeEqAbsMulVecLe.lean) — the counterexample, and {x \| \|zᵢᵀx\| ≤ 1} as the parallelotope of the columns of Z⁻¹ **Counterexample:** `Zonotope.parallelotope_eq_abs_mulVec_le_counterexample` | `fixed` — Σ[-1, 1]·2 = [-2, 2] but {2x ≤ 1, -2x ≤ 1} = [-1/2, 1/2]; {Vx ≤ 1} is the parallelotope of Z⁻¹'s columns, the reading the reduction needs; see Findings |
| `Eq. 30` | R₁(Π) = maxᵢ ‖vᵢ‖₁ ≤ maxᵢ n‖vᵢ‖∞ = nR∞(Π). | [`L1NormLeCardMulNorm.lean`](../../src/CORALean/Global/Counterexamples/L1NormLeCardMulNorm.lean), [`L1NormLeCardMulNorm.lean`](../../src/CORALean/Global/L1NormLeCardMulNorm.lean) — the counterexample to the equality, and ‖x‖₁ ≤ n‖x‖∞, which gives R₁(Π) ≤ nR∞(Π) on any set **Counterexample:** `l1_norm_le_card_mul_norm_counterexample` | `fixed` — the first equality is false (the rows ±eᵢ have ‖·‖₁ = 1, the corner (1, 1) has 2); the inequality R₁(Π) ≤ nR∞(Π), all that is used, holds; see Findings |
| `Eq. 34` | Π^Δ × [α, (2n-1)α] ⊂ Z*, the zonotope Z* = Σᵢ [0, 1](vᵢ + αe_{n+1}). | n/a — "as proven in [17]" (Burger and Gritzmann 2000), cited and not proved here | `restated` |
| `Lemma 5` | For β ∈ [0, α], (β/α)Π^Δ × {β} = Z* ∩ (ℝⁿ × {β}) (Eq. 36), and Eq. 35 at β = α. | [`SliceEqSmulConvexHull.lean`](../../src/CORALean/Global/SliceEqSmulConvexHull.lean) — any N ≥ 1 points vᵢ, Π^Δ their convex hull | `proof-gap` — the printed proof divides by β (λᵢ = (α/β)μᵢ), undefined at β = 0, where the slice is {0} for another reason |
| `Lemma 6` | There is a vertex q of the largest cube C ⊂ Z* centered at c that touches ∂Z* with qᵀe_{n+1} ∈ [0, α]. | [`ExistsCubeVertexMemFrontierLift.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ExistsCubeVertexMemFrontierLift.lean) — Π = {x \| \|zᵢᵀx\| ≤ 1} as for `Eq. 29`, α of `Eq. 31` with R∞(Π) the greatest ‖x‖∞ on Π, Z* of `Eq. 33` in `Vec ℝ n × ℝ` under the maximum norm; the largest cube exists, and a vertex on ∂Z* at height in [0, α] | `proof-gap` — the zones I-IV do not cover Z*, (39)'s r∞(Z*) ≤ (2n - 2)α fails at n = 1, and the bound the conclusion needs, r∞(Z*) ≥ (n - 1)α, is not argued; see Findings |
| `Thm. 2` | INRAD∞ (does r∞(Z) ≤ k hold?) is NP-hard. | — | — |
| `Cor. 4` | ZC is co-NP-complete. | — | — |
| `Alg. 1` | (venum) Z₁ ⊆ Z₂ iff no vertex v of Z₁ has ‖v - c₂‖_{Z₂} > 1. | [`Venum.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Venum.lean), [`VenumIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/VenumIff.lean), [`ConstructEqConvexHullCorner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ConstructEqConvexHullCorner.lean) — vertices read as the 2^{m₁} sign corners; exact | `underspecified` — the listing takes any zonotopes, but ‖·‖_{Z₂} exists only for non-degenerate Z₂ (`Def. 4`) |
| `Alg. 2` | (polymax) For each facet ηᵢ of Z₂, the sign vector xⱼ = sign(ηᵢᵀgⱼ/hᵢ); Z₁ ⊆ Z₂ iff none has ‖x - c₂‖_{Z₂} > 1. | [`Polymax.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Polymax.lean), [`PolymaxIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/PolymaxIff.lean) — the vertex c₁ + G₁x tested, the halfspace representation of Z₂ - c₂ supplied (hᵢ ≠ 0); exact | `underspecified` — the listing tests the sign vector x ∈ ℝ^{m₁} itself against c₂ ∈ ℝⁿ, writes νᵢ for ηᵢ, and needs the facets of Z₂ moved to the origin for the signs to be right |
| `Eq. 46` | 2(m₂ choose n-1) ≤ 2(em₂/(n-1))^{n-1}. | [`ChooseLeExpMulDivPow.lean`](../../src/CORALean/Global/ChooseLeExpMulDivPow.lean) | `correct` |
| `Eq. 47` | (opt) d(Z₁, Z₂) is the maximum of f(x) = ‖G₂x + c₁ - c₂‖_{Z₂} over x ∈ {-1, 1}^{m₁}, by convexity. | [`IsGreatestZonotopeNormCorner.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IsGreatestZonotopeNormCorner.lean) — the maximum over Z₁ is the maximum over its sign corners | `underspecified` — G₂x is misprinted for G₁x, the inbody's generators |
| `Sec. 5` | Runtime and accuracy of venum, polymax, opt and st on random zonotope pairs (Figs. 2-6). | n/a — experiments | `not-a-claim` |

## Findings

**`Lemma 1` — the unit ball.** `Def. 3` admits any hᵢ ≠ 0, and the lemma says the unit ball
{S_P ≤ 1} "corresponds to the polytope P". That needs the origin inside P: for
P = [1, 2] = {x ≤ 2, -x ≤ -1}, S_P(0) = 0 ≤ 1 and 0 ∉ P (the unit ball is (-∞, 1]). With
every hᵢ > 0 the unit ball is P, and a symmetric S_P is then a norm (`P` bounded leaves no
direction with S_P = 0). The paper only ever uses zonotopes centered at the origin, where
hᵢ > 0 holds. [`PolyNormIsAsymmNorm.lean`](../../src/CORALean/ContSet/HPolytope/Real/Counterexamples/PolyNormIsAsymmNorm.lean)

**`Remark 2` — no polyhedral norm for a degenerate zonotope.** The remark offers S_Z as a
norm that works where ‖·‖_Z is not defined. But S_Z needs a halfspace representation with
every hᵢ ≠ 0; for a degenerate Z centered at 0 every representation has some hᵢ = 0, since
hᵢ ≥ 0 at the origin and with all of them positive {Hx < h} is an open set around 0 inside
Z. Nor can any norm stand in, a norm's unit ball having an interior.
[`NotExistsPolyNormOfDegenerate.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/NotExistsPolyNormOfDegenerate.lean)

**`Eq. 29`, `Eq. 30` — the parallelotope of the reduction.** (29) writes
Π = Σᵢ[-1, 1]zᵢ = {x | Vx ≤ 1} with V the rows ±zᵢ; in ℝ¹ with z₁ = 2 the first is [-2, 2]
and the second [-1/2, 1/2]. The rows ±zᵢ cut out the parallelotope of the columns of Z⁻¹,
and that is the reading under which the next sentence, Π^Δ = conv(±zᵢ), is right. (30) then
writes R₁(Π) = maxᵢ‖vᵢ‖₁, the maximum over the rows — vertices of Π^Δ, not of Π: for
zᵢ = eᵢ in ℝ², every row has ‖vᵢ‖₁ = 1 while Π's corner (1, 1) has 2. Only the inequality
R₁(Π) ≤ nR∞(Π) is used afterwards, and it holds pointwise. Whether Π is read as Σᵢ[-1, 1]zᵢ
or as {Vx ≤ 1} matters to `Thm. 2`, which takes its NP-hardness from Bodlaender et al. for
one of the two; neither the theorem nor that citation is formalized here.
[`ParallelotopeEqAbsMulVecLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/ParallelotopeEqAbsMulVecLe.lean),
[`L1NormLeCardMulNorm.lean`](../../src/CORALean/Global/Counterexamples/L1NormLeCardMulNorm.lean)

**`Lemma 6` — the proof.** The statement holds (for linearly independent zᵢ and Π read as
{x | |zᵢᵀx| ≤ 1}, as `Eq. 29` needs), but the proof does not establish it. Its zones I-IV are
said to hold every point of Z* "in exactly one" of them, yet a point of the box's side faces
(‖s‖∞ = r∞(Π^Δ), t ∈ (α, (2n - 1)α)) is in none. Its bound (39), r∞(Z*) ≤ min{r∞(Π^Δ),
(2n - 2)α}, is false at n = 1: there Z* is the parallelogram with vertices 0, (z₁, α), (-z₁, α)
and (0, 2α), and the square of radius α/2 around c = (0, α) lies in it, so r∞(Z*) > 0 =
(2n - 2)α. And the conclusion, a vertex at height nα - r∞(Z*) ∈ [0, α], needs r∞(Z*) ≥ (n - 1)α,
a lower bound the proof never states. It holds: the cube of radius (n - 1)α around c fits in Z*,
its horizontal part inside Π^Δ because its coefficients aᵢ in the basis zᵢ have ∑|aᵢ| ≤
n(n - 1)αR∞(Π) ≤ 1/2 (`Eq. 32`), its vertical part inside [α, (2n - 1)α] (`Eq. 34`). With that, a
maximal cube has a vertex on ∂Z* (a cube whose vertices all lay inside could grow, being their
hull), an upper one mirrors through c, and the lower vertices sit at height nα - r∞(Z*) ∈
[0, α], r∞(Z*) ≤ nα since Z* lies between heights 0 and 2nα.
[`ExistsCubeVertexMemFrontierLift.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ExistsCubeVertexMemFrontierLift.lean)

**Minor.** `Eq. 20` prints the cube as [-1, -1]ⁿ; `Eq. 47` prints G₂ for G₁; `Lemma 3`
needs b ≠ 0. `Lemma 5`'s proof divides by β; `Alg. 2` tests the sign vector in place of the
vertex it selects. Each is read as the argument intends.
