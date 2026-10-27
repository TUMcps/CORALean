# Billiard walk - a new sampling algorithm for control and optimization

```bibtex
@article{polyak2014billiard,
  author = {Polyak, B. T. and Gryazina, E. N.},
  title = {Billiard walk - a new sampling algorithm for control and optimization},
  journal = {IFAC Proceedings Volumes},
  year = {2014}
}
```

**Source:** https://skoge.folk.ntnu.no/prost/proceedings/ifac2014/media/files/2312.pdf (the IFAC World Congress preprint of the paper, 6 pages numbered 6123-6128 as in the proceedings, with the IFAC copyright line; all pages read in full, text extracted with `pypdf`). The typeset volume, <https://doi.org/10.3182/20140824-6-ZA-1003.02312>, was not read. Not the arXiv preprint 1211.3932, "Random sampling: Billiard Walk algorithm" (Gryazina and Polyak, 22 pages, European Journal of Operational Research 238(2), 2014): a different, longer paper, which was not used.  
**Inventory:** unconfirmed (against the congress preprint; the typeset proceedings may differ in wording or numbering. The preprint's numbered items are the Billiard Walk algorithm, Theorems 1-2, equations (1)-(4), Tables 1-3 and Figures 1-4)

The paper behind CORA's `'uniform:billiardWalk'` sampler (`randPoint_` of `zonotope` and `conZonotope`): a Hit-and-Run
variant whose next point is the end of a billiard trajectory of random exponential length, reflecting at the boundary.
What is formalized is its deterministic part for a set given by inequalities `(aᵢ, x) ≤ bᵢ`: the boundary oracle of
Eq. 1 (the chord, exact at an interior point), the reflection law, the trajectory with corners and the reflection
limit `R` handled as step 4 says, and that its end stays in the polytope. The paper's theorems are about the Markov
chain the algorithm induces (asymptotic uniformity) and rest on Smith 1984; they are `not-covered`, the local
ingredients being the reflection law, its involution and, from Smith, the invariance of the uniform law under a
symmetric density. CORA's coverage row for `randPoint_` is `out-of-scope` (`random/sampling`).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Alg.` | (Billiard Walk) 1. x₀ ∈ Int Q, i = 0. 2. ℓ = -τ log η, η uniform on [0, 1]. 3. Draw d uniform on the unit sphere (d = ξ/‖ξ‖, ξ standard Gaussian) and build the billiard trajectory from xᵢ along d, the direction changing at a boundary with internal normal s, ‖s‖ = 1, as d → d - 2(d, s)s. 4. Compute the end of the trajectory of length ℓ; if a point with nonsmooth boundary is met or the number of reflections exceeds R, go to step 2. 5. xᵢ₊₁ is the end point. | [`BilliardStep.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/BilliardStep.lean), [`BilliardEnd.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/BilliardEnd.lean), [`BilliardReflect.lean`](../../src/CORALean/Global/BilliardReflect.lean), [`BilliardReflectLaw.lean`](../../src/CORALean/Global/BilliardReflectLaw.lean), [`BilliardReflectReflect.lean`](../../src/CORALean/Global/BilliardReflectReflect.lean), [`BilliardEndMem.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/BilliardEndMem.lean), [`BilliardStepMem.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/BilliardStepMem.lean) — one `let` per printed step, for a polytope `{x \| (aᵢ, x) ≤ bᵢ}` in a finite-dimensional real inner product space; the reflection is `d - 2(d, s)s` for `‖s‖ = 1` (`‖d'‖ = ‖d‖`, `(d', s) = -(d, s)`, an involution); the end of the trajectory lies in the polytope from any interior point, any `ℓ ≥ 0` and any `R` | `underspecified` — the draws `η`, `ξ` are arguments and "go to step 2" is `none`, the caller redrawing. "nonsmooth" is read as a hit point on a second hyperplane (unspecified for a polytope); `ℓ` exactly a segment length ends on the boundary (unspecified); see Findings |
| `Eq. 1` | The Boundary Oracle for Q = {x \| (aᵢ, x) ≤ bᵢ}: tᵢ = (bᵢ - (aᵢ, xₖ))/(aᵢ, d), t̲ = max_{i: tᵢ<0} tᵢ, t̄ = min_{i: tᵢ>0} tᵢ, the segment of the line xₖ + td in Q being [t̲, t̄]. | [`HitTime.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/HitTime.lean), [`ChordHighIndex.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/ChordHighIndex.lean), [`ChordLowIndex.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/ChordLowIndex.lean), [`ChordHigh.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/ChordHigh.lean), [`ChordLow.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/ChordLow.lean), [`MemAddSmulIffChord.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/MemAddSmulIffChord.lean), [`HitAndRunStep.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/HitAndRunStep.lean) — `x + t d` satisfies every inequality exactly when `t̲ ≤ t ≤ t̄`, from a point with every inequality strict (Q is open in the paper); an absent end is no constraint | `correct` |
| `Sec. 2.3` | Normals: for a polytope s = aᵢ, i an index where the maximum or minimum in (1) is achieved; the reflection d → d - 2(d, s)s with ‖s‖ = 1. For a boundary point X⁰ of an LMI X ≽ 0 the normal is S = eeᵀ, e the eigenvector of the zero eigenvalue, and the matrix direction changes as D → D - 2 trace(DS)S. | [`FacetNormal.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/FacetNormal.lean), [`BilliardReflect.lean`](../../src/CORALean/Global/BilliardReflect.lean) — the unit normal of row `i` is the Riesz representative of `P.A i` divided by its length; the reflection is written over any real inner product space, which includes the trace inner product | `underspecified` — `s = aᵢ` is a unit vector only after normalizing the row; the sign is outward where the paper says internal, which the reflection does not see |
| `Sec. 2.3 (LMI)` | For the matrix set Q = {X ∈ Sⁿˣⁿ \| X ≻ 0, AX + XAᵀ ≼ 0}, A stable, a random direction is a symmetric D with ‖D‖_F = 1. The Boundary Oracle L = {t \| X⁰ + tD ∈ Q} = (t̲, t̄) with t̲ = min λᵢ, t̄ = max μᵢ over the positive real eigenvalues λᵢ of the pencil (X⁰, -D) and the negative real eigenvalues μᵢ of (AX⁰ + X⁰Aᵀ - H, -(AD + DAᵀ)). | — | — |
| `Thm. 1` | Q open, bounded, convex with piecewise smooth boundary: the distribution of the points xᵢ of the BW algorithm tends to the uniform one, lim_{N→∞} P_N(A \| x) = λ(A) for every measurable A ⊆ Q and every x. Proof: Smith's Thm. 2 (symmetric density, positive density); the density exists as the cone and length-interval probabilities are proportional to the volume. Positivity as every point is reachable with no reflection; symmetry from the uniform direction and the reversibility of a billiard trajectory. | n/a — not-covered: convergence of a general-state Markov chain (Smith's Thm. 2, via Doob) is not in Mathlib, and the density symmetry needs a measure on trajectories. The local ingredients are proved: the reflection is an involution that preserves the speed (`BilliardReflectReflect`, `BilliardReflectLaw`), the walk stays in Q (`BilliardEndMem`), and a symmetric density leaves its reference measure invariant (Smith's Lemma 1) | `not-covered` |
| `Thm. 2` | Q connected, bounded, open, piecewise smooth boundary, any two points joined by a piecewise-linear path in Q of at most B + 1 linear parts: the distribution of the xᵢ tends to uniform in the same sense. Proof: p_N(y\|x) > 0 for N > B, reversibility p_N(y\|x) = p_N(x\|y), and the subsequences xᵢ, x_{N+i}, ... are asymptotically uniform. | n/a — not-covered: as Thm. 1 | `not-covered` |
| `Sec. 2.1` | Choice of the parameters: for τ small BW behaves as a ball walk of radius τ; fast convergence is empirically seen for τ ≈ diam Q; the reflection limit is R = 10n. | n/a — a recommendation, with no claim to prove | `not-a-claim` |
| `Sec. 2.2` | Preliminary transformation: a linear scaling of an ill-shaped Q, or T = (∇²F(x*))^{-1/2} for a barrier F, can improve the shape; a simplex cannot be improved. | n/a — a remark | `not-a-claim` |
| `Sec. 3.1` | Plane angle α < π: a billiard trajectory quits the angle after no more than N* = ⌈π/α⌉ reflections, for any start and direction; Hit-and-Run quits with probability 1 - (1 - α/π)^N after N iterations, 1 - 1/e after N*; for a polyhedral cone a billiard trajectory escapes after at most M reflections, M independent of the data (Tabachnikov, Thm. 7.17). | — | — |
| `Sec. 3.2` | Orthant {x > 0} in ℝⁿ: a billiard trajectory quits after at most n reflections (the set I = {i \| dᵢ < 0} shrinks at each reflection); Hit-and-Run quits with probability 2^{-(n-1)} per iteration. | — | — |
| `Sec. 3.3` | Concave corner: for the domain (2) the number of reflections of a trajectory with ℓ = 1, d = (-1, 0) from x⁰ = [0.9; ε] grows without bound as ε decreases (Table 2); the rare bad directions give 5.2 reflections per point on average over 200 points. | n/a — an experiment | `not-a-claim` |
| `Sec. 3.4` | Unit cube (0, 1)ⁿ: the next point of BW has the explicit form kᵢ = ⌊xᵢ + ℓdᵢ⌋, yᵢ = xᵢ + ℓdᵢ - kᵢ for kᵢ even, 1 - (xᵢ + ℓdᵢ - kᵢ) for kᵢ odd. | — | — |
| `Sec. 3.5` | Simplex Q = {xᵢ > 0, Σxᵢ = 1}: the enclosed simplices S_α = {xᵢ ≥ α, Σxᵢ = 1} have volume ratio f(α) = vol S_α/vol S₀ = (1 - (n + 1)α)ⁿ. | — | — |
| `Sec. 3.6` | The toroid (3) satisfies Theorem 2 with B = ⌈π/(2 arccos((1 - r)/(1 + r))⌉ + 1, "no more than B linear parts". | — | — |
| `Sec. 4` | Global optimization by multistart on the most distant point in a cube (4): the largest and smallest local solutions are f_max = Σ(1 + \|aᵢ\|)², f_min = Σ(1 - \|aᵢ\|)². | — | — |
| `Eq. 2` | The domain Q = {x ∈ ℝ² \| -x₁⁴ < x₂ < x₁⁴, x₁ ≥ 1} of the concave-corner test. | n/a — the definition of a test set | `not-a-claim` |
| `Eq. 3` | The toroid Q = {x ∈ ℝⁿ \| ‖x - c_x‖ ≤ r}, c_{xᵢ} = xᵢ/√(x₁² + x₂²) for i = 1, 2 and 0 otherwise. | n/a — the definition of a test set | `not-a-claim` |
| `Eq. 4` | The most distant point problem max ‖x - a‖₂ over -1 ≤ xᵢ ≤ 1. | n/a — the definition of a test problem | `not-a-claim` |
| `Table 1` | Mean and standard deviation of the BW reflections and of the HR iterations needed to quit the angle α, 5000 runs from [0; 0.1]: BW 2.28 (0.87), 3.08 (1.3), 5.94 (2.93), 25.08 (14.46) for α = π/2, π/4, π/10, π/50; HR 2.37, 3.75, 8.23, 39.25. | n/a — an experiment | `not-a-claim` |
| `Table 2` | Reflections of the billiard trajectory in domain (2) against ε: 746, 1851, 2480, 3617, 6158, 13496 for ε = 1e-3 ... 1.1e-4, more than 5e+6 at 1.01e-4. | n/a — an experiment | `not-a-claim` |
| `Table 3` | The probability of 1% relative accuracy by multistart with 1000 samples on (4): 0.9995, 0.95, 0.7 for n = 20, 25, 30. | n/a — an experiment | `not-a-claim` |

## Findings

**Alg. — normals and corners.** Step 3 reflects at a boundary "with internal normal s, ‖s‖ = 1", and Sec. 2.3 takes
`s = aᵢ` for a polytope. The row of `(aᵢ, x) ≤ bᵢ` is a unit vector only if the inequality is normalized, and it points
outward; `d - 2(d, s)s` with a non-unit `s` is not a reflection (the length of `d` is not preserved), so the
normal is divided by `‖aᵢ‖` in `HPolytope.facetNormal`. Step 4 says to restart "if a point with nonsmooth boundary is
met"; for a polytope that is a point on more than one hyperplane, and the check is what keeps the walk inside: at the
edge of two hyperplanes a reflection at one can leave a direction pointing out of the other. `billiardEnd_mem`
holds with the check and from an interior point. The step also does not say what happens when `ℓ` equals a segment
length exactly, the end lying on the boundary; CORA (`l <= step_segmentLength`) and `billiardEnd` both end the trajectory
there, and the event has probability zero.

**Eq. 1 — the starting point.** The formula is exact for a point with every inequality strict. At a point on a
hyperplane with `(aᵢ, d) > 0` the row has `tᵢ = 0`, which `t̄ = min_{tᵢ>0} tᵢ` skips, and the formula
returns a chord running out of `Q`. Q is open in the paper and `xₖ ∈ Q`, so the formula is used as stated; the walk
reaches boundary points only through its reflections, where `(aᵢ, d') < 0` makes the skipped row correct.

**Table 1 — what is counted.** The text says the rows are the number of billiard reflections to quit the angle, which
Sec. 3.1 bounds by `N* = ⌈π/α⌉`: at most 2 for `α = π/2`. The BW entry for `α = π/2` is 2.28 (standard deviation 0.87),
above that maximum, so the column cannot be a reflection count. A simulation of the printed setup (the cone
`|x₁| ≤ x₂ tan(α/2)`, start `[0; 0.1]`, uniform direction, count the reflections until the line `x₂ = 1`) gives means
0.97, 1.92, 4.81, 24.2 for `α = π/2, π/4, π/10, π/50`, with maxima 2, 4, 10, 50 = `⌈π/α⌉`, which confirms the bound and
not the table; the table's meaning is not recoverable from the text.

**Eq. 2 — the domain.** `Q = {-x₁⁴ < x₂ < x₁⁴, x₁ ≥ 1}` is unbounded and does not contain the starting point
`x⁰ = [0.9; ε]` of the experiment; with `x₁ ≤ 1` it is the bounded cusp the trajectory bounces in, and Fig. 2 plots
`x₁ ∈ [-0.5, 1.5]`. The inequality is read as a typo for `x₁ ≤ 1`.

**Thm. 2 and Sec. 3.6 — the path length.** Theorem 2 asks for a path "of no more than B + 1 linear parts"; Sec. 3.6
verifies it "with B = ⌈π/(2 arccos((1-r)/(1+r)))⌉ + 1, i.e. ... no more than B linear parts". One of the two is off by one.

**Thm. 1 and Thm. 2 — the proofs.** The existence and symmetry of the transition density are argued by cones of
trajectories, "the area of reflection with a smooth boundary can be approximated as plain region": a sketch, not a
proof, and the reflection limit `R` (which truncates trajectories) is not part of the density being symmetrized.
The conclusion for a polytope follows from the symmetry of the unfolded trajectory, as for Smith's chain; the
formalization does not carry this out (`not-covered`).

**CORA.** `randPoint_` ('uniform:billiardWalk') follows the algorithm (`tau = norm(Z,2,'ub')`,
`R0 = 10 dim`, the length `tau * -log(unifrnd(0,1))`, the end ending at `l <= step_segmentLength`),
with the facet normal and the chord from linear programs. Its zonotope version tests for a nonsmooth
point by counting the generator coefficients `|λⱼ| = 1` in the chord LP,
`extremeCounter <= m - 2 || extremeCounter == m`. For a facet point of a zonotope in general
position that count is `m - n + 1` (the `n - 1` generators parallel to the facet are free), which is
`m - 1` for `n = 2` and at most `m - 2` for `n ≥ 3`. A simulation of the LP (HiGHS, random
full-dimensional zonotopes) returns exactly this, so in dimension three and up every reflection
looks like a corner and the trajectory restarts, and the walk is a truncated ball-style walk and not
a billiard. This does not return a point outside the set. It is not a witnessed bug (no Lean
statement about the solver), and is recorded here only. The `conZonotope` version has no corner
test.
