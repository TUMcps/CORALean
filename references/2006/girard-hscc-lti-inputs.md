# Efficient Computation of Reachable Sets of Linear Time-Invariant Systems with Inputs

```bibtex
@inproceedings{girard2006efficient,
  author = {Girard, A. and Le Guernic, C. and Maler, O.},
  title = {Efficient Computation of Reachable Sets of Linear Time-Invariant Systems with Inputs},
  booktitle = {Hybrid Systems: Computation and Control},
  year = {2006}
}
```

**In the paper's bibliography.**

**Source:** https://www-verimag.imag.fr/~maler/Papers/zonotope.pdf (the authors' 15-page manuscript, linked from O. Maler's publication list, read in full; `pypdf` extracts no readable text from it, its fonts being Type 3 without a character map, so it was read from page images rendered with PyMuPDF; the Springer chapter, <https://doi.org/10.1007/11730637_21>, was not reachable from the environment, and HAL's record hal-00171555 carries no file)  
**Inventory:** confirmed (against the manuscript; its numbered items are Definitions 1-2, Algorithms 1-2, Propositions 1-3, Lemma 1, Theorem 1, Remarks 1-2 and equations (1)-(3); the unnumbered statements that make a claim are rows named by section)

The paper behind CORA's `linearSys` wrapping-free scheme (`priv_reach_wrappingfree`, `post`,
"method implemented from Algorithm 2 in [1]"): the recurrence `Ω_{i+1} = ΦΩᵢ ⊕ U` is split
into `X_{i+1} = ΦXᵢ`, `V_{i+1} = ΦVᵢ` and `S_{i+1} = Sᵢ ⊕ Vᵢ`, so the linear map only ever
acts on sets of fixed size (`Alg. 1`), and taking the interval hull of `Vᵢ` before it is
summed keeps `Sᵢ` a box without the error compounding (`Alg. 2`, `Prop. 1`). Both algorithms
are formalized on zonotopes over the discrete-time system `LinearSysDT`, `Φ` its matrix, with
their output identified exactly: `Alg. 1` returns the reachable sets, `Alg. 2` their interval
hulls. CORA runs the continuous-time version, whose first window and input set come from the
time discretization the paper leaves to [ADG03, G05]; that is Althoff's thesis `Alg. 2`,
`LinearSys.reachBox`. The `S`-band and under-approximation sections are formalized for one
zonotope, and the control synthesis of Sec. 5.2 is proved as printed; the printed closure
of `S`-band intersections under Minkowski sum is false, see Findings.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | The recurrence `Ω_{i+1} = ΦΩᵢ ⊕ U`, `i ∈ ℕ`, `Φ` a `d × d` matrix, `U` a convex bounded subset of `ℝᵈ`, `⊕` the Minkowski sum; unrolled, `Ω_{i+1} = Φ^{i+1}Ω₀ ⊕ ΦⁱU ⊕ … ⊕ U`. | [`GlmReachEq.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/GlmReachEq.lean) — `Ωᵢ` is `LinearSysDT.reachSetExact`, the sets reached in exactly `i` steps of `x_{k+1} = Φx_k + u_k`, `u_k ∈ U` | `correct` |
| `Eq. 2` | The auxiliary sequences `X₀ = Ω₀`, `X_{i+1} = ΦXᵢ`, `V₀ = U`, `V_{i+1} = ΦVᵢ`, `S₀ = {0}`, `S_{i+1} = Sᵢ ⊕ Vᵢ`; then `X_{i+1} = Φ^{i+1}Ω₀`, `V_{i+1} = Φ^{i+1}U`, `S_{i+1} = ΦⁱU ⊕ … ⊕ U`, and `Ω_{i+1} = X_{i+1} ⊕ S_{i+1}`. | [`GlmReachEq.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/GlmReachEq.lean) (`LinearSysDT.aux_glmReach_inv`: `Xᵢ ⊕ Sᵢ = Ωᵢ` and `Sᵢ ⊕ Vᵢ = ΦSᵢ ⊕ U`, the closed forms read one step at a time) | `correct` |
| `Alg. 1` | (Reachability of linear time-invariant systems) Input `Φ`, `Ω₀`, `U` and `N`; `X₀ ← Ω₀`, `V₀ ← U`, `S₀ ← {0}`; for `i` from `0` to `N - 1`: `X_{i+1} ← ΦXᵢ`, `S_{i+1} ← Sᵢ ⊕ Vᵢ`, `V_{i+1} ← ΦVᵢ`, `Ω_{i+1} ← X_{i+1} ⊕ S_{i+1}`; return `{Ω₁, …, Ω_N}`, the first `N` terms of the sequence (1). | [`GlmReach.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/GlmReach.lean) (`LinearSysDT.glmReach`, one `let` per printed line, on zonotopes as in Sec. 3), [`GlmReachEq.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/GlmReachEq.lean) (`LinearSysDT.glmReach_eq`: the `i`-th set returned denotes `Ω_{i+1}` exactly) — the terms returned are `Ω₁, …, Ω_N`, those after `Ω₀`; neither convexity nor boundedness of `U` is used | `correct` |
| `Def. 1` | (Zonotope) `(u, ⟨v₁, …, v_m⟩) = {u + Σⱼ αⱼvⱼ \| αⱼ ∈ [-1, 1]}`; order `m/d`. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Sec. 3` | Zonotopes are closed under linear maps, `ΦZ = (Φu, ⟨Φv₁, …, Φv_m⟩)`, and under Minkowski sum, `Z₁ ⊕ Z₂ = (u₁ + u₂, ⟨v₁, …, v_m, w₁, …, w_n⟩)`. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 3` | `Box`, mapping a set `E ⊆ ℝᵈ` to its interval hull, the smallest Cartesian product of intervals containing `E`, satisfies `Box(E₁ ⊕ E₂) = Box(E₁) ⊕ Box(E₂)` for every `E₁, E₂ ⊆ ℝᵈ`. | [`HullAdd.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/HullAdd.lean) (`Interval.hull_add`), and at zonotopes `LinearSysDT.aux_interval_plus` in [`GlmReachBoxEqHull.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/GlmReachBoxEqHull.lean) — `Box` is `Interval.hull`, coordinatewise infimum and supremum | `underspecified` — an unbounded `E` has intervals with infinite ends for a hull, which `Interval` does not represent; nonempty bounded `E₁`, `E₂` are supplied (the paper applies it only to zonotopes) |
| `Alg. 2` | (Interval hull approximation of the reachable sets) As `Alg. 1`, with `S_{i+1} ← Sᵢ ⊕ Box(Vᵢ)` and `Ω̄_{i+1} ← Box(X_{i+1}) ⊕ S_{i+1}`; `Xᵢ`, `Vᵢ` zonotopes, `Sᵢ`, `Ω̄ᵢ` interval products; return `{Ω̄₁, …, Ω̄_N}`. | [`GlmReachBox.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/GlmReachBox.lean) (`LinearSysDT.glmReachBox`, one `let` per printed line, `Box` of a zonotope `Zonotope.interval`); its output is `Prop. 1` | `correct` |
| `Prop. 1` | For all `i ∈ {1, …, N}`, `Ω̄ᵢ` is the interval hull of the set `Ωᵢ`. | [`GlmReachBoxEqHull.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/GlmReachBoxEqHull.lean) (`LinearSysDT.glmReachBox_eq_hull`: the list returned is `Interval.hull` of `reachSetExact` at `1, …, N`) | `correct` |
| `Remark 1` | Algorithm 2 works for any pair of set classes, the first closed under linear maps, the second under Minkowski sum with constant size, `Box` replaced by an approximation with a property like (3). | n/a — a remark on generality, its instance being Sec. 4.2 | `not-a-claim` |
| `Def. 2` | (`S`-band intersection) For `S = {s₁, …, s_ℓ}` and `m, M ∈ ℝ^ℓ`, `[m, M]_S = {x ∈ ℝᵈ \| mᵢ ≤ sᵢ·x ≤ Mᵢ, i = 1, …, ℓ}`. | [`BoxS.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/BoxS.lean) — `ContSet.hyperplanePolyhedron S m M`, the bounds indexed by the direction itself | `correct` |
| `Sec. 4.2` | `S`-band intersections are closed under Minkowski sum: `[m₁, M₁]_S ⊕ [m₂, M₂]_S = [m₁ + m₂, M₁ + M₂]_S`; and `Box_S(Z₁ ⊕ Z₂) = Box_S(Z₁) ⊕ Box_S(Z₂)`, so `S`-band intersections can replace interval hulls in Algorithm 2. | [`HyperplanePolyhedronAddSubset.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HyperplanePolyhedronAddSubset.lean) (`ContSet.hyperplanePolyhedron_add_subset`: `⊆`), [`ExistsHyperplanePolyhedronAddNe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/ExistsHyperplanePolyhedronAddNe.lean) (two nonempty bands in the plane, `S = {e₁, e₂, e₁ + e₂}`, whose sum is not the band of the summed bounds), [`BoxSPlus.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/BoxSPlus.lean) (`Zonotope.boxS_plus`: the bounds of `Box_S(Z₁ ⊕ Z₂)` are the sums of the bounds) — the run of Algorithm 2 with `S`-bands is not written out as an algorithm; its step is `boxS_plus` **Counterexample:** `ContSet.exists_hyperplanePolyhedron_add_ne` | `fixed` — the printed equality fails when a bound is not attained; true as `⊆`, which is what Algorithm 2 needs, and with `Box_S` of zonotopes, whose bounds are attained; see Findings |
| `Prop. 2` | For a zonotope `Z = (u, ⟨v₁, …, v_m⟩)`, `Box_S(Z) = [m, M]_S` with `mᵢ = sᵢ·u - Σⱼ\|sᵢ·vⱼ\|`, `Mᵢ = sᵢ·u + Σⱼ\|sᵢ·vⱼ\|` is an over-approximation of `Z`, and each face of `Box_S(Z)` has at least one common point with `Z`. | [`BoxS.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/BoxS.lean) (`Zonotope.boxS`), [`BoxSTight.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/BoxSTight.lean) (`Zonotope.boxS_tight`: `Z ⊆ Box_S(Z)`, and for every `s ∈ S` points of `Z` with `s·x = m_s` and with `s·x = M_s`) | `correct` |
| `Prop. 3` | With `Ω̄ᵢ = Box_S(Ωᵢ)` computed by Algorithm 2 with `S`-bands and the guard `G_e = {x \| n_e·x = f_e}`, if `n_e ∈ S` then `Ω̄ᵢ` intersects `G_e` iff `Ωᵢ` intersects `G_e`. | [`BoxSInterHyperplaneIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/BoxSInterHyperplaneIff.lean) (`Zonotope.boxS_inter_hyperplane_iff`) — for any zonotope `Ωᵢ`, `Ω̄ᵢ` read as `Box_S(Ωᵢ)` as the statement does | `correct` |
| `Remark 2` | A step of Algorithm 2 meets a guard exactly when Algorithm 1's would, but the intersections differ, so after the transition Algorithm 2 starts from a larger set: the wrapping effect returns at discrete transitions. | n/a — a remark; its first half is `Prop. 3` | `not-a-claim` |
| `Sec. 5.1` | The under-approximation of `Z` by its extremal points along `S`: those along `sᵢ` are `u ± gᵢ`, `gᵢ = Σⱼ sign(sᵢ·vⱼ)vⱼ`, and `Z̲ = (u, [g₁, …, g_ℓ]_S) = ConvexHull({u ± gᵢ, i ∈ {1, …, ℓ}}) = {u + Σᵢ αᵢgᵢ : Σᵢ\|αᵢ\| ≤ 1}`. | [`ExtremalGen.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ExtremalGen.lean) (`Zonotope.extremalGen`, `gᵢ`, `sign` zero at zero), [`ExtremalGenExtremal.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ExtremalGenExtremal.lean) (`Zonotope.extremalGen_extremal`: `u ± g` are points of `Z` maximizing and minimizing `x·s`), [`UnderS.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/UnderS.lean) (`Zonotope.underS`, `Z̲` in the `α` form), [`UnderSSubset.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/UnderSSubset.lean) (`Zonotope.underS_subset`: `Z̲ ⊆ Z`), [`UnderSEqConvexHull.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/UnderSEqConvexHull.lean) (`Zonotope.underS_eq_convexHull`: the `α` form is the convex hull of the `u ± gᵢ`) | `underspecified` — at `ℓ = 0`, `S` empty, the hull is empty and the `α` form is `{u}`; `0 < ℓ` is supplied |
| `Lemma 1` | With `(u, [g₁, …, g_ℓ]_S) ⊞ (u', [g'₁, …, g'_ℓ]_S) = (u + u', [g₁ + g'₁, …, g_ℓ + g'_ℓ]_S)`, for two zonotopes `Z`, `Z'`: the under-approximation of `Z ⊕ Z'` is `Z̲ ⊞ Z̲'`. | [`ExtremalGenPlus.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ExtremalGenPlus.lean) (`Zonotope.extremalGen_plus`: `Z ⊕ Z'` has center `u + u'` and extremal offset `gᵢ + g'ᵢ` along every direction) — at the representation, which is what `⊞` acts on | `correct` |
| `Thm. 1` | With `Ω̄ᵢ` the `S`-band over-approximation of `Ωᵢ` and `Ω̲ᵢ` its under-approximation, if the normal `n_e` of the guard `G_e` is in `S` then `Ω̲ᵢ` intersects `G_e` iff `Ω̄ᵢ` intersects `G_e` iff `Ωᵢ` intersects `G_e`. | [`UnderSInterHyperplaneIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/UnderSInterHyperplaneIff.lean) (`Zonotope.underS_inter_hyperplane_iff`) — for any zonotope `Ωᵢ` and `n_e = s_j` | `correct` |
| `Sec. 5.2` | Control synthesis: for `y ∈ Ω̲_N`, `y = u + Σⱼ αⱼgⱼ` with `Σⱼ\|αⱼ\| ≤ 1`, where by Lemma 1 `u = u^N + … + u⁰` and `gⱼ = g^N_j + … + g⁰_j` for the under-approximations `(u^N, [g^N]_S)` of `Φ^NΩ₀` and `(uⁱ, [gⁱ]_S)` of `ΦⁱU`, and `Φ` invertible, `x₀ = Φ^{-N}(u^N + Σⱼ αⱼg^N_j)` and `vᵢ = Φ^{i+1-N}(u^{N-1-i} + Σⱼ αⱼg^{N-1-i}_j)` give `x₀ ∈ Ω₀`, `vᵢ ∈ U`, and `x_{i+1} = Φxᵢ + vᵢ` reaches `x_N = y`. | [`ControlOfMemUnderS.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ControlOfMemUnderS.lean) (`LinearSysDT.control_of_mem_underS`, through `Z̲ ⊆ Z` of Sec. 5.1) — `y` given in the summed form the paper reads off Lemma 1, `Φ^{i+1-N}` as `(Φ⁻¹)^{N-1-i}`, invertibility as a unit determinant | `correct` |
| `Sec. 6` | Experiments: a five-dimensional system over `N` up to 1000 steps (Fig. 3, Table 1), random systems up to `d = 200` (Table 2), and the effect of the time step (Fig. 4), against Zono-20 and Zono-5. | n/a — experiments, and running-time and memory figures | `not-a-claim` |

## Findings

**Sec. 4.2 — the sum of two `S`-band intersections.** The paper states that "the class of
`S`-band intersections is closed under the Minkowski sum: `[m₁, M₁]_S ⊕ [m₂, M₂]_S = [m₁ + m₂,
M₁ + M₂]_S`". The equality fails as soon as a bound is not attained. In the plane, with
`S = {e₁, e₂, e₁ + e₂}`, `P₁ = [(0, 0, 0), (1, 1, 9)]_S` is the unit square, its bound `9` along
`e₁ + e₂` slack, and `P₂ = [(0, 0, 0), (9, 9, 1)]_S` the unit triangle, its bounds `9` along `e₁`
and `e₂` slack. The band of the summed bounds is `[(0, 0, 0), (10, 10, 10)]_S` and holds
`(10, 0)`, while every point of `P₁ ⊕ P₂` has first coordinate at most `2`
(`exists_hyperplanePolyhedron_add_ne`). No two directions are parallel and both sets are
nonempty, so nothing degenerate is used. What holds is the inclusion `⊆`
(`hyperplanePolyhedron_add_subset`), which is all the over-approximating use in Algorithm 2
needs; and for `Box_S` of zonotopes, whose bounds are attained ([1, Prop. 2]), the band of
the summed bounds is `Box_S` of the zonotope sum (`boxS_plus`). The use the paper makes of
the identity, `S`-bands in place of interval hulls with `Ω̄ᵢ = Box_S(Ωᵢ)`, rests on these two.
[`ExistsHyperplanePolyhedronAddNe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/ExistsHyperplanePolyhedronAddNe.lean), [`HyperplanePolyhedronAddSubset.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HyperplanePolyhedronAddSubset.lean), [`BoxSPlus.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/BoxSPlus.lean)
