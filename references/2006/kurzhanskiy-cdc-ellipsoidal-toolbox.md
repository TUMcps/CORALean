# Ellipsoidal Toolbox (ET)

A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". In Proc. of the 45th IEEE Conference on Decision and Control (CDC), pp. 1498-1503, 2006.

**Source:** http://lihodeev.com/pubs/2006CDC_EllipsoidalToolbox.pdf, read through the Wayback Machine (the first author's copy, 6 pages, read in full; text extracted with `pdftotext`; it is the conference paper, pages 1498-1503 of the proceedings, DOI 10.1109/CDC.2006.377036, not the longer ET manual. IEEE Xplore was not reachable.)  
**Inventory:** confirmed (the paper numbers only equation (1), the system of Sec. III, and has no numbered definitions, lemmas or theorems; every paragraph that makes a claim is a row named by section and topic)

The paper that introduces the Ellipsoidal Toolbox, cited by CORA's ellipsoid operations
(`@ellipsoid/ellipsoid`, `plus`, `minkDiff`, `distance`, `and_` and their private helpers).
Section II states the ellipsoidal calculus the toolbox implements, as closed forms: the
support function, the affine image, when a Minkowski difference is nonempty, the distances
from an ellipsoid to a point, an ellipsoid and a hyperplane, and the cut by a hyperplane. All
of these are formalized, in the tree's generator form `E = q + G B₂` with shape `Q = G Gᵀ`. The
distance formulas are correct, and so is the sign test for a hyperplane. The paper's sentence
that the distance is *negative* for a point inside or for intersecting sets fails on the
boundary, where it is `0`. The approximations of sums, differences and reach sets by families
of ellipsoids are restated from the authors' earlier work, and the closed-loop reach sets of
Section III are a subject CORALean does not cover.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. I` | A survey of other reachability tools (MPT, d/dt, zonotopes, CheckMate, level sets, Requiem), and ET's benefits: the reach-set representation grows quadratically with the dimension and linearly with the number of time steps, and the approximations are arbitrarily accurate. | n/a — a survey and a description of the toolbox | `not-a-claim` |
| `Sec. II (support function)` | The ellipsoid `E(q, Q)`, `Q = Qᵀ ≽ 0`, is the set with `ρ(l \| E(q, Q)) = ⟨l, q⟩ + ⟨l, Q l⟩^{1/2}` for all `l`. | [`SupportFuncEq.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/SupportFuncEq.lean), [`IsGreatestDot.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/IsGreatestDot.lean) — the support function of `q + G B₂` is `⟨l, q⟩ + ⟨l, G Gᵀ l⟩^{1/2}`, attained | `correct` |
| `Sec. II (affine map)` | `A E(q, Q) + b = E(A q + b, A Q Aᵀ)` for `A ∈ ℝ^{m×n}`; with `b = 0` and orthonormal rows it is the projection onto the subspace those rows span. | [`AffineImageExact.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/AffineImageExact.lean) — exact, centre `A q + b`, generator `A G`, whose shape is `A Q Aᵀ` by `Ellipsoid.shape_mtimes` | `correct` |
| `Sec. II (Minkowski sum)` | The Minkowski sum of `k` ellipsoids is not in general an ellipsoid, but is the union of internal and the intersection of external ellipsoids `E⁻_l`, `E⁺_l` over directions `l`, more accurate with more directions. | n/a — restated from Kurzhanski and Vályi's *Ellipsoidal Calculus for Estimation and Control* [3], which has no page here; the external family is `Ellipsoid.plus_outer` | `restated` |
| `Sec. II (Minkowski difference)` | `E(q₁, Q₁) -̇ E(q₂, Q₂) = {x \| x + E(q₂, Q₂) ⊆ E(q₁, Q₁)}` is nonempty iff `E(0, Q₂) ⊆ E(0, Q₁)`. | [`MinkowskiDiffNonemptyIff.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/MinkowskiDiffNonemptyIff.lean) | `correct` |
| `Sec. II (bad directions)` | The difference is the union of internal and the intersection of external ellipsoids over `l`, which exist only for directions that are not bad: `l` is bad if `⟨l, Q₁ l⟩^{1/2} / ⟨l, Q₂ l⟩^{1/2} > λ`, `λ` the least root of `det(Q₁ - λ Q₂)`. | n/a — restated from Kurzhanski and Vályi [3], which has no page here | `restated` |
| `Sec. II (hyperplane)` | `H(v, c) = {x \| ⟨v, x⟩ = c}`, and ET reads it as the halfspace `⟨v, x⟩ ≤ c`. | n/a — a definition and a toolbox convention | `not-a-claim` |
| `Sec. II (distances)` | `dist(E(q, Q), a) = max_{⟨l, l⟩ = 1} (⟨l, a⟩ - ⟨l, q⟩ - ⟨l, Q l⟩^{1/2})`; `dist(E(q₁, Q₁), E(q₂, Q₂)) = max_{⟨l, l⟩ = 1} (⟨l, q₁⟩ - ⟨l, Q₁ l⟩^{1/2} - ⟨l, q₂⟩ - ⟨l, Q₂ l⟩^{1/2})`; `dist(E(q, Q), H(v, c)) = (\|c - ⟨v, q⟩\| - ⟨v, Q v⟩^{1/2}) / ⟨v, v⟩^{1/2}`. | [`DistPointEqMax.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/DistPointEqMax.lean), [`DistEllipsoidEqMax.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/DistEllipsoidEqMax.lean), [`DistHyperplaneEq.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/DistHyperplaneEq.lean), [`NearestPointSeparates.lean`](../../src/CORALean/Global/NearestPointSeparates.lean) — for disjoint sets each maximum is the Euclidean distance, attained | `correct` |
| `Sec. II (sign of the distance)` | The distance is negative if the point is inside the ellipsoid, or the two ellipsoids, or the ellipsoid and the hyperplane, intersect. | [`DistPointNonneg.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Counterexamples/DistPointNonneg.lean), [`DistPointEqMax.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/DistPointEqMax.lean), [`DistEllipsoidEqMax.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/DistEllipsoidEqMax.lean), [`DistHyperplaneEq.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/DistHyperplaneEq.lean) — `≤ 0`, not `< 0`; for the hyperplane, `E ∩ H ≠ ∅` iff the value is `≤ 0`; the counterexample is `E(0, 1) ⊂ ℝ`, `a = 1` **Counterexample:** `Ellipsoid.dist_point_nonneg_counterexample` | `fixed` — on the boundary, or for touching sets, the value is `0`; see Findings |
| `Sec. II (hyperplane intersection)` | If nonempty, the intersection of an ellipsoid and a hyperplane is an ellipsoid. | [`InterHyperplaneEq.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/InterHyperplaneEq.lean) — with the cut's centre and generator given explicitly | `correct` |
| `Sec. II (intersection approximations)` | The intersection of two ellipsoids, or of an ellipsoid and a halfspace, is not in general an ellipsoid, but has a minimum-volume external and a maximum-volume internal ellipsoid. | n/a — restated from Kurzhanski and Vályi [3], which has no page here | `restated` |
| `Eq. 1` | The system `ẋ = A(t) x + B(t) u(t, x) + G(t) v(t)` with control in `E(p(t), P(t))` and disturbance in `E(q(t), Q(t))`, reducing to an affine system for `Q ≡ 0` and a linear one for `G ≡ 0`. | n/a — the system the section studies | `not-a-claim` |
| `Sec. III (closed-loop reach set)` | The reach set under closed-loop control against every disturbance can be empty, and `E(0, G Q Gᵀ) ⊆ E(0, B P Bᵀ)` on `[t₀, t]` suffices for it to be nonempty; without disturbance it is the open-loop reach set and is never empty. | n/a — closed-loop reach sets of a control-disturbance game, a subject CORALean does not cover | `not-covered` |
| `Sec. III (ellipsoidal families)` | The reach set is compact and convex and, when nonempty, the union of internal and the intersection of external ellipsoids `E(x_c(t), X^∓_l(t))`, whose shape matrices solve differential equations in `l`. | n/a — restated from Kurzhanski and Varaiya [4], [5], which have no page here | `restated` |
| `Sec. III (directions)` | More directions give a better approximation at cost linear in their number; no universal rule chooses them; refinement with extra directions helps decide intersections. | n/a — advice on using the toolbox | `not-a-claim` |
| `Sec. III (semigroup)` | The forward and backward closed-loop reach sets satisfy the semigroup property, which `evolve` implements, also for switched systems. | n/a — closed-loop reach sets, a subject CORALean does not cover | `not-covered` |
| `Sec. III (backward reach set)` | The backward reach set is convex and compact and, when nonempty, approximated by ellipsoidal families. | n/a — closed-loop backward reach sets, a subject CORALean does not cover | `not-covered` |
| `Sec. III (discrete time)` | The same methods extend to discrete-time affine systems, following [6], without disturbances; backward reach sets need nonsingular `A[k]`. | n/a — restated from Varaiya's earlier work [6], which has no page here, and a toolbox limitation | `restated` |
| `Sec. IV` | Plotting routines for ellipsoids, sums, differences and reach sets in 2-D and 3-D, and projections for higher dimensions. | n/a — visualization | `not-a-claim` |
| `Sec. V` | A two-mode hybrid system with a hyperplane guard, run in ET. | n/a — an example | `not-a-claim` |

## Findings

**`Sec. II (sign of the distance)` — zero, not negative.** "The distance is negative if the
point is inside the ellipsoid, or the two ellipsoids and the ellipsoid and hyperplane have a
non-empty intersection." Inside means in the closed set, and on its boundary the formula is
`0`: for `E(0, 1) = [-1, 1]` and `a = 1`, `l = 1` gives `1 - 0 - 1 = 0`, and no unit `l` gives
more, so the maximum is `0`. Two ellipsoids that touch, and an ellipsoid tangent to a
hyperplane, give `0` the same way (`[-1, 1]` and `[1, 3]`; `[-1, 1]` and `H(1, 1)`). The
corrected statement is `≤ 0`, which holds for all three formulas. For the hyperplane it is
an equivalence: `E ∩ H` is nonempty iff the value is `≤ 0`. CORA's
`priv_distanceHyperplane` computes the paper's hyperplane formula and notes only that it
"can be <0", which is right (read from the source, not run). [`DistPointNonneg.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Counterexamples/DistPointNonneg.lean), [`DistHyperplaneEq.lean`](../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/DistHyperplaneEq.lean)
