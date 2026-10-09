# Avoiding Geometric Intersection Operations in Reachability Analysis of Hybrid Systems

M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM International Conference on Hybrid Systems: Computation and Control (HSCC), 2012, pp. 45-54.

**Source:** https://mediatum.ub.tum.de/download/1285848/1285848.pdf (the paper as published at HSCC'12, Beijing, April 17-19, 2012, ACM 978-1-4503-1220-2/12/04, 10 pages, read in full; text extracted with `pypdf`. CORA's headers give the year as 2011 or 2012; the paper's own copyright line says HSCC'12, and the TUM research portal gives pp. 45-54, doi:10.1145/2185632.2185643.)  
**Inventory:** confirmed (Definitions 1-3, Lemma 1, Theorem 1 and Propositions 1-3, each with its own counter; equations (1)-(19))

The origin of CORA's `guardIntersect_hyperplaneMap`: instead of intersecting the
reachable set with a halfspace guard, map the last reachable set before the guard onto
it. The map is computed for a constant flow first, then for a "state-dependent constant
flow" whose error to the linear dynamics is a set `E`, and its nonlinear dependence on the
initial state is enclosed by a second-order Taylor series whose Hessian is a matrix
zonotope — which is where the paper's quadratic maps come from.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Hybrid Automaton) HA = (V, X, U, T, g, h, f), without invariants, guards halfspaces {x \| nᵀx ≤ d}, jumps affine x' = Kx + l; transitions urgent, taken as soon as a guard is hit. | [`HybridAutomaton.lean`](../../src/CORALean/HybridDynamics/HybridAutomaton.lean) — the tuple, a location's invariant being the whole space and a guard any `ContSet`; [`UrgentRun.lean`](../../src/CORALean/HybridDynamics/Definitions/UrgentRun.lean) — the urgent semantics, a run whose every stay meets no guard before its end, and [`UrgentRunToRun.lean`](../../src/CORALean/HybridDynamics/Theorems/UrgentRunToRun.lean) — every urgent run is a `Run`, so the enclosures proved of `Run` hold of the urgent runs | `correct` |
| `Def. 2` | (Exact Reachable Set) R^e_{v_i}(r): the continuous states x(r) of trajectories (v(t), x(t)) of HA with v(0) = v_0, x(0) ∈ X_0 and v(r) = v_i. | — | — |
| `Eq. 1` | Under constant flow ż = b the hyperplane is hit at z_h = Cz_0 + w, C = I - bnᵀ/(nᵀb), w = bd/(nᵀb); a state within E of that flow hits it in x_h ∈ (Cx_0 + w) ⊕ (-bnᵀ/(nᵀb) ⊗ E) ⊕ E. | [`ConstFlowHitSet.lean`](../../src/CORALean/HybridDynamics/Definitions/ConstFlowHitSet.lean), [`MemConstFlowHitSet.lean`](../../src/CORALean/HybridDynamics/Theorems/MemConstFlowHitSet.lean) — a state `x₀ + bt + e`, `e ∈ E`, on `nᵀx = d` lies in the set, at `nᵀb ≠ 0` | `correct` |
| `Eq. 3` | The solution of the state-dependent constant flow ẏ = Ay_0 + b (eq. 2) is y(t) = y_0 + (Ay_0 + b)t. | [`SdcFlow.lean`](../../src/CORALean/HybridDynamics/Operations/SdcFlow.lean), [`HasDerivAtSdcFlow.lean`](../../src/CORALean/HybridDynamics/Theorems/HasDerivAtSdcFlow.lean) | `correct` |
| `Eq. 5` | The solution of ẋ = Ax + u_c from x_0 is x(t) = e^{At}x_0 + Γ(t)u_c, Γ(t) = ∫₀ᵗ e^{A(t-τ)}dτ. | [`VariationOfConstants.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/VariationOfConstants.lean), [`ExpIntegralConstInput.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExpIntegralConstInput.lean) — every trajectory is its variation-of-constants formula, and at a constant input the integral is `expIntegral A t *ᵥ u_c`; [`MulExpIntegral.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/MulExpIntegral.lean) — `Γ(t) = A⁻¹(e^{At} - I)` at an invertible `A` | `correct` |
| `Eq. 6` | e^{At} ∈ Σᵢ₌₀^η (At)ⁱ/i! ⊕ Ê(t), Ê(t) = [-W(t), W(t)], W(t) = \|Σᵢ>η Aⁱtⁱ/i!\| ≤ e^{\|A\|t} - Σᵢ₌₀^η \|A\|ⁱtⁱ/i!. | [`ExpRemainderMat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Definitions/ExpRemainderMat.lean), [`ExpSubExpTaylorMemExpRemainderInterval.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpSubExpTaylorMemExpRemainderInterval.lean) — at `t ≥ 0`, the paper's times | `correct` |
| `Eq. 7` | Γ(t) = Σᵢ Aⁱtⁱ⁺¹/(i+1)! ∈ Σᵢ₌₀^η Aⁱtⁱ⁺¹/(i+1)! ⊕ Ẽ(t), where one can choose Ẽ(t) = Ê(t)t, see [3]. | [`AbsParticularTailEntryLe.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/AbsParticularTailEntryLe.lean) — `expIntegral`, which is `Γ`'s series, less its sum to `η` is entrywise within `Ê(t)t` | `correct` |
| `Prop. 1` | (Minimizing the State Difference) e(t̃_h) = x(t̃_h) - y(t̃_h) is minimized by b = Θ(t̃_h)x_0 + Γ*(t̃_h)u_c, Θ(t) = Σᵢ₌₂^η Aⁱtⁱ⁻¹/i!, Γ*(t) = Σᵢ₌₀^η Aⁱtⁱ/(i+1)!, such that lim_{η→∞} e(t̃_h) = 0. | [`SdcInput.lean`](../../src/CORALean/HybridDynamics/Definitions/SdcInput.lean), [`TendstoSdcFlowError.lean`](../../src/CORALean/HybridDynamics/Theorems/TendstoSdcFlowError.lean) — the limit, at the paper's `ξ = x₀` | `underspecified` — "minimized" holds only in the limit `η → ∞`, which is what the proposition goes on to state and what is proved; at a fixed `η` another `b` makes the error `0`; see Findings |
| `Def. 3` | (Matrix Zonotope) Z = {C + Σ βᵢG^(i) \| βᵢ ∈ [-1, 1]}, written (C, G^(1), ..., G^(p)); order p/n. | n/a — restated; tracked as `Eq. 8` on [Althoff, Krogh, Stursberg 2011](../2011/althoff-reachability-parametric-uncertainties.md) | `restated` |
| `Eq. 10` | Z_1 ⊕ Z_2 = (c + d, g^(1), ..., h^(p_2)) and L ⊗ Z_1 = (Lc, Lg^(1), ..., Lg^(p_1)). | n/a — restated from [19]; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 11` | [-1, 1] ⊗ Z_1 ⊆ (0, c, g^(1), ..., g^(p_1)). | [`UnitIntervalMul.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/UnitIntervalMul.lean), [`UnitIntervalMulOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/UnitIntervalMulOuter.lean) — over any real module | `correct` |
| `Lemma 1` | (Quadratic Map) Z_Q = {λ \| λᵢ = xᵀQ^(i)x, x ∈ Z} is enclosed by the zonotope with dᵢ = cᵀQ^(i)c + 0.5 Σₛ g^(s)ᵀQ^(i)g^(s), h^(j)ᵢ = cᵀQ^(i)g^(j) + g^(j)ᵀQ^(i)c, h^(p+j)ᵢ = 0.5 g^(j)ᵀQ^(i)g^(j), and h^(2p+l)ᵢ = g^(j)ᵀQ^(i)g^(k) + g^(k)ᵀQ^(i)g^(j) for j < k. | [`QuadMap.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/QuadMap.lean), [`QuadMapOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/QuadMapOuter.lean) — the pair block indexed by all `(j, k)` and zero off `j < k`, `p + p + p²` generators denoting the same set  | `correct` |
| `Lemma 1 (complexity)` | Computing the enclosing zonotope of the quadratic map has complexity O(n⁵). | n/a — a running time stated of the construction, which the tree can only assert (`Cost/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Lemma 1 (generators)` | The enclosing zonotope of the quadratic map has σ = C(p+2, 2) - 1 generators. | — partial: `Zonotope.quadMap` (in `QuadMap.lean`, which cites `Lemma 1`; whose pair block is indexed by all `(j, k)` and zero off `j < k`, so it has `p + p + p²` generators, the extra ones zero); missing: the count σ as a theorem about the result, which needs the pair block indexed by `j < k` alone or the zero generators dropped, and the generator count of the zonotope as a `Complexity/` fact | — |
| `Thm. 1` | (Matrix Zonotope Map) With Q^(i) ∈ Q^(i) = (D^(i), K^(i,1), ..., K^(i,ν)), {λ \| λᵢ = xᵀQ^(i)x, x ∈ Z, Q^(i) ∈ Q^(i)} is enclosed by Z_D ⊕ ([-1, 1] ⊗ Z_K(1)) ⊕ ... ⊕ ([-1, 1] ⊗ Z_K(ν)), the parts by Lemma 1, (10) and (11); complexity O(n⁶). | [`QuadMapMatZono.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/QuadMapMatZono.lean), [`QuadMapMatZonoOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/QuadMapMatZonoOuter.lean), [`QuadMapMatZonoNotOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/QuadMapMatZonoNotOuter.lean) — the enclosure with one factor `βⱼ` per generator shared by every coordinate, as the proof's eq. (12) has it, and the counterexample for factors chosen per coordinate; the complexity is not formalized **Counterexample:** `Zonotope.quadMapMatZono_not_outer` **Counterexample:** `Zonotope.quadMapMatZono_not_outer` | `fixed` — the printed set lets each `Q^(i)` range over its matrix zonotope on its own, and then the enclosure fails (`λ = (1, -1)` against the segment from `(-1, -1)` to `(1, 1)`); it holds with the factors shared, as the proof assumes; see Findings |
| `Sec. 5.2` | The range [ω̲, ω̄] of (nᵀ ⊗ Z) ⊕ (-d), ω̲ = ω_c - Σ\|ω^(i)\|, ω̄ = ω_c + Σ\|ω^(i)\|: "if ω̲ ≥ 0, no intersection occurs and if ω̄ ≤ 0, the reachable set is completely in the guard set". | [`HalfspaceRange.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/HalfspaceRange.lean), [`HalfspaceRangeSound.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HalfspaceRangeSound.lean), [`HalfspaceRangeNonnegNotDisjoint.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HalfspaceRangeNonnegNotDisjoint.lean) — the second test as printed, the first at `ω̲ > 0`, and the one-point counterexample at `ω̲ = 0` **Counterexample:** `Zonotope.halfspaceRange_nonneg_not_disjoint` **Counterexample:** `Zonotope.halfspaceRange_nonneg_not_disjoint` | `fixed` — `ω̲ ≥ 0` does not exclude an intersection, the zonotope may touch the closed halfspace; corrected to `ω̲ > 0`; see Findings |
| `Eq. 13` | The set of abstraction errors E = {x(t) - y(t) \| t ∈ T; x_0, y_0 ∈ ξ ⊕ Y} = T(⊕ᵢ₌₂^η (Aⁱ/i!)(T^{i-1}(ξ ⊕ Y) ⊕ (-t̃_h^{i-1}ξ)) ⊕ ⊕ᵢ₌₀^η Aⁱ(Tⁱ ⊕ (-t̃_hⁱ))/(i+1)! u_c) ⊕ Ê(t_max)x_0 ⊕ Ê(t_max)t_max u_c. | [`TrajectoryError.lean`](../../src/CORALean/HybridDynamics/Operations/TrajectoryError.lean), [`TrajectoryErrorOuter.lean`](../../src/CORALean/HybridDynamics/Theorems/TrajectoryErrorOuter.lean) — the right-hand side as CORA computes it (`LinearSys.trajectoryError`, the series cut at `η + 1`, `f₁ = f₂`): every `x(t) − y(t)` with `t ∈ [t_min, t_max]`, `0 ≤ t_min`, `x₀ ∈ ξ ⊕ Y`, `x` the solution of eq. (5) and `y` the flow of eq. (3) from the same `x₀` with `b` of `Prop. 1` at `t̃_h = tc`, lies in it. The index of the second sum starts at `1` in CORA, its `i = 0` term being `0`; outer only | `underspecified` — the right-hand side is an enclosure, not the set (cut at `η`, `Ê` for the rest), and `y` starts at the same `x₀` as `x`; see Findings |
| `Eq. 15` | R_h(x_0) = x_0 + (Ax_0 + b)(d - nᵀ(x_0 ⊕ E))/(nᵀ(Ax_0 + b)) ⊕ E encloses the states x_h hitting H, split as y_h(x_0) ⊕ R_{h,E}(x_0). | [`HitSet.lean`](../../src/CORALean/HybridDynamics/Definitions/HitSet.lean), [`MemHitSet.lean`](../../src/CORALean/HybridDynamics/Theorems/MemHitSet.lean) — in the split form; a state `x₀ + (Ax₀ + b)t + e`, `e ∈ E` (eq. 14), on `nᵀx = d` lies in it, at `nᵀ(Ax₀ + b) ≠ 0` | `correct` |
| `Prop. 2` | (Partial derivatives of y_h) With Λ(y) = nᵀ(Ay + b), Υ = nᵀA, Θ(y) = -nΛ(y) - (d - nᵀy)Υᵀ, Ω = -nΥ + Υᵀnᵀ: L_il = ∂y_{h,i}/∂x_0l = I_il + A_il(d - Σⱼ nⱼx_0j)/Λ + (Σⱼ A_ij x_0j + bᵢ)Θ_l/Λ², and ∂²y_{h,i}/∂x_0l∂x_0m = Q^(i)_lm/Λ², Q^(i)_lm = A_il Θ_m + A_im Θ_l + (Ω_lm - 2Θ_lΥ_m/Λ)(Σⱼ A_ij x_0j + bᵢ). | [`HitPoint.lean`](../../src/CORALean/HybridDynamics/Definitions/HitPoint.lean), [`HitJacobian.lean`](../../src/CORALean/HybridDynamics/Definitions/HitJacobian.lean), [`HitHessian.lean`](../../src/CORALean/HybridDynamics/Definitions/HitHessian.lean), [`HasDerivAtHitPoint.lean`](../../src/CORALean/HybridDynamics/Theorems/HasDerivAtHitPoint.lean), [`HasDerivAtHitJacobian.lean`](../../src/CORALean/HybridDynamics/Theorems/HasDerivAtHitJacobian.lean) — as partial derivatives along the axes, `L_im` differentiated along `l` for the second, wherever `Λ ≠ 0`; the printed `Θ_l(x_0)/Λ(x_0) 2Υ_m` read as `2Θ_lΥ_m/Λ`, the reading Prop. 3's `ψ_{c,l}2Υ_m` confirms | `correct` |
| `Prop. 3` | (Taylor Series of y_h) y_{h,i}(x_0) ∈ (y_{h,i}(ξ) + L_i(ξ)ν) ⊕ ½νᵀQ̃^(i)ν, ν = x_0 - ξ, Q̃^(i) = [φ̲, φ̄] ⊗ Q^(i) with [φ̲, φ̄] ⊇ {1/Λ(x_0)²} and Q^(i) enclosed by the matrix zonotope (C̃^(i), G̃^(i,1), ..., G̃^(i,1+2p)). | — | — |
| `Sec. 5.4` | R_g = y_h(ξ) ⊕ L ⊗ (R(0) ⊕ (-ξ)) ⊕ ½[φ̲, φ̄] ⊗ R_quad ⊕ R_{h,E}(R(0)), R_quad by Thm. 1, encloses the guard intersection; complexity O(n⁶). | — | — |
| `Sec. 6` | Powertrain with backlash, up to 101 states, against the geometric approach and SpaceEx (Tables 1-2, Figs. 5-8). | n/a — an experiment, not a claim to formalize | `not-a-claim` |

## Findings

**`Thm. 1` — whose factors.** The theorem's set is `{λ | λᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z, Q⁽ⁱ⁾ ∈ Q⁽ⁱ⁾}`,
each `Q⁽ⁱ⁾` a matrix zonotope of its own, so the coordinates may pick their matrices
independently. The proof's eq. (12) writes `λᵢ = xᵀ(D⁽ⁱ⁾ + Σⱼ βⱼK⁽ⁱ'ʲ⁾)x` with one `βⱼ` for all
`i`, and the enclosure `Z_D ⊕ ([-1, 1] ⊗ Z_K(1)) ⊕ ...` needs exactly that: `[-1, 1] ⊗ Z_K(j)`
scales all coordinates by one factor. At `n = ν = 1`, `m = 2`, `Z = {1}`, `D⁽ⁱ⁾ = 0` and
`K⁽ⁱ'¹⁾ = 1`, independent factors reach `λ = (1, -1)`, while the enclosure is the segment from
`(-1, -1)` to `(1, 1)`. The application in Sec. 5.4 is unaffected: there all `Q⁽ⁱ⁾(x₀)` depend
on one `x₀`, so their factors are shared.
[`QuadMapMatZonoNotOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/QuadMapMatZonoNotOuter.lean),
[`QuadMapMatZonoOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/QuadMapMatZonoOuter.lean)

**`Sec. 5.2` — the boundary.** "If `ω̲ ≥ 0`, no intersection occurs": the guard
`{x | nᵀx ≤ d}` is closed, and at `ω̲ = 0` the zonotope reaches its boundary, so it meets the
guard — the zonotope `{0}` against `{x | x ≤ 0}` in one dimension. What holds is `ω̲ > 0`.
[`HalfspaceRangeNonnegNotDisjoint.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HalfspaceRangeNonnegNotDisjoint.lean),
[`HalfspaceRangeSound.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HalfspaceRangeSound.lean)

**`Eq. 13` — an enclosure, from one start.** The right-hand side cuts both Taylor series at `η` and
bounds what is left by `Ê(t_max)x₀` and `Ê(t_max)t_max u_c`, so it contains the set of errors, which is
not equal to it. `x₀, y₀ ∈ ξ ⊕ Y` is also read with the two starts one point: `y` is the flow `y₀ + (Ay₀ + b)t`
and a `y₀` apart from `x₀` would put `x₀ − y₀` into the error at every `t`, which the right-hand side
does not hold; the theorem takes `y₀ = x₀`. The sum over `i = 0` of the input terms is `0`
(`Tⁱ ⊖ t̃_hⁱ` at `i = 0`) and CORA starts it at `1`. At order `η = 0` the error would hold `−Ax₀t`, which
the right-hand side does not: the theorem is for `η ≥ 1`, as `Prop. 1`'s Taylor polynomial is.
[`TrajectoryErrorOuter.lean`](../../src/CORALean/HybridDynamics/Theorems/TrajectoryErrorOuter.lean)

**`Prop. 1` — "minimized".** The proposition says `b = Θ(t̃_h)x₀ + Γ*(t̃_h)u_c` minimizes the
error `e(t̃_h)`, "such that `lim_{η→∞} e(t̃_h) = 0`". At a fixed `η` it does not: since
`y(t̃_h) = x₀ + (Ax₀ + b)t̃_h` is affine in `b`, `b = (x(t̃_h) - x₀)/t̃_h - Ax₀` makes the error
exactly `0` for `t̃_h ≠ 0`, while the printed `b` leaves the truncation's remainder. The
proposition's content is the limit, which is what is formalized; it also needs `η ≥ 1`
before `x₀ + Ax₀t + tΘ(t)x₀` is the exponential's Taylor polynomial.
[`TendstoSdcFlowError.lean`](../../src/CORALean/HybridDynamics/Theorems/TendstoSdcFlowError.lean)
