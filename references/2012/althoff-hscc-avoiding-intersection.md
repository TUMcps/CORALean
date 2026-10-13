# Avoiding Geometric Intersection Operations in Reachability Analysis of Hybrid Systems

M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM International Conference on Hybrid Systems: Computation and Control (HSCC), 2012, pp. 45-54.

**Source:** https://mediatum.ub.tum.de/download/1285848/1285848.pdf (the paper as published at HSCC'12, Beijing, April 17-19, 2012, ACM 978-1-4503-1220-2/12/04, 10 pages, read in full; text extracted with `pypdf`. CORA's headers give the year as 2011 or 2012; the paper's own copyright line says HSCC'12, and the TUM research portal gives pp. 45-54, doi:10.1145/2185632.2185643.)  
**Inventory:** confirmed (Definitions 1-3, Lemma 1, Theorem 1 and Propositions 1-3, each with its own counter; equations (1)-(19))

The origin of CORA's `guardIntersect_hyperplaneMap`: instead of intersecting the
reachable set with a halfspace guard, map the last reachable set before the guard onto
it. The map is computed for a constant flow first, then for a "state-dependent constant
flow" whose error to the linear dynamics is a set `E`, and its nonlinear dependence on the
initial state is enclosed by a second-order Taylor series whose Hessian is a matrix
zonotope — which is where the paper's quadratic maps come from. That Hessian enclosure is false
with the paper's coordinatewise bound on `Θ/Λ` (`Prop. 3`); with `Θ/Λ` bounded as a vector, the
composition `R_g` of `Sec. 5.4` encloses every `R_h(x₀)`, by an exact remainder rather than the
paper's coordinatewise Taylor argument.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Hybrid Automaton) HA = (V, X, U, T, g, h, f), without invariants, guards halfspaces {x \| nᵀx ≤ d}, jumps affine x' = Kx + l; transitions urgent, taken as soon as a guard is hit. | [`HybridAutomaton.lean`](../../src/CORALean/HybridDynamics/HybridAutomaton.lean) — the tuple, a location's invariant being the whole space and a guard any `ContSet`; [`UrgentRun.lean`](../../src/CORALean/HybridDynamics/Definitions/UrgentRun.lean) — the urgent semantics, a run whose every stay meets no guard before its end, and [`UrgentRunToRun.lean`](../../src/CORALean/HybridDynamics/Theorems/UrgentRunToRun.lean) — every urgent run is a `Run`, so the enclosures proved of `Run` hold of the urgent runs | `correct` |
| `Def. 2` | (Exact Reachable Set) R^e_{v_i}(r): the continuous states x(r) of trajectories (v(t), x(t)) of HA with v(0) = v_0, x(0) ∈ X_0 and v(r) = v_i. | [`UrgentReachSetAt.lean`](../../src/CORALean/HybridDynamics/Definitions/UrgentReachSetAt.lean) — `UrgentRunAt`, an urgent run of `Def. 1` lasting r in all, and `urgentReachSetAt`, its end states at v_i from X_0 at v_0; [`UrgentReachSetAtSubsetReachSet.lean`](../../src/CORALean/HybridDynamics/Theorems/UrgentReachSetAtSubsetReachSet.lean) — inside the time-free `reachSet`, so its enclosures hold at every r | `correct` |
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
| `Lemma 1 (complexity)` | Computing the enclosing zonotope of the quadratic map has complexity O(n⁵). | n/a — a running time stated of the construction, which the tree can only assert (`Complexity/Time/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Lemma 1 (generators)` | The enclosing zonotope of the quadratic map has σ = C(p+2, 2) - 1 generators. | [`QuadMapTri.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/QuadMapTri.lean), [`QuadMapPairIdx.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/QuadMapPairIdx.lean), [`QuadMapTriOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/QuadMapTriOuter.lean), [`QuadMapTri.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Space/QuadMapTri.lean) — `Zonotope.quadMapTri` is the lemma's zonotope with the pair block over `j < k` alone, numbered by `quadMapPairIdx`; it encloses the quadratic map (`quadMapTri_outer`) and has `C(p + 2, 2) - 1` generators (`quadMapTri_h`), `p` linear, `p` squares and `C(p, 2)` pairs | `correct` |
| `Thm. 1` | (Matrix Zonotope Map) With Q^(i) ∈ Q^(i) = (D^(i), K^(i,1), ..., K^(i,ν)), {λ \| λᵢ = xᵀQ^(i)x, x ∈ Z, Q^(i) ∈ Q^(i)} is enclosed by Z_D ⊕ ([-1, 1] ⊗ Z_K(1)) ⊕ ... ⊕ ([-1, 1] ⊗ Z_K(ν)), the parts by Lemma 1, (10) and (11). | [`QuadMapMatZono.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/QuadMapMatZono.lean), [`QuadMapMatZonoOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/QuadMapMatZonoOuter.lean), [`QuadMapMatZonoNotOuter.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/QuadMapMatZonoNotOuter.lean) — the enclosure with one factor `βⱼ` per generator shared by every coordinate, as the proof's eq. (12) has it, and the counterexample for factors chosen per coordinate **Counterexample:** `Zonotope.quadMapMatZono_not_outer` | `fixed` — the printed set lets each `Q^(i)` range over its matrix zonotope on its own, and then the enclosure fails (`λ = (1, -1)` against the segment from `(-1, -1)` to `(1, 1)`); it holds with the factors shared, as the proof assumes; see Findings |
| `Thm. 1 (complexity)` | The complexity of the matrix zonotope map with respect to the dimension n is O(n⁶). | n/a — a running time stated of the construction, which the tree can only assert (`Complexity/Time/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Sec. 5.2` | The range [ω̲, ω̄] of (nᵀ ⊗ Z) ⊕ (-d), ω̲ = ω_c - Σ\|ω^(i)\|, ω̄ = ω_c + Σ\|ω^(i)\|: "if ω̲ ≥ 0, no intersection occurs and if ω̄ ≤ 0, the reachable set is completely in the guard set". | [`HalfspaceRange.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/HalfspaceRange.lean), [`HalfspaceRangeSound.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HalfspaceRangeSound.lean), [`HalfspaceRangeNonnegNotDisjoint.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HalfspaceRangeNonnegNotDisjoint.lean) — the second test as printed, the first at `ω̲ > 0`, and the one-point counterexample at `ω̲ = 0` **Counterexample:** `Zonotope.halfspaceRange_nonneg_not_disjoint` **Counterexample:** `Zonotope.halfspaceRange_nonneg_not_disjoint` | `fixed` — `ω̲ ≥ 0` does not exclude an intersection, the zonotope may touch the closed halfspace; corrected to `ω̲ > 0`; see Findings |
| `Eq. 13` | The set of abstraction errors E = {x(t) - y(t) \| t ∈ T; x_0, y_0 ∈ ξ ⊕ Y} = T(⊕ᵢ₌₂^η (Aⁱ/i!)(T^{i-1}(ξ ⊕ Y) ⊕ (-t̃_h^{i-1}ξ)) ⊕ ⊕ᵢ₌₀^η Aⁱ(Tⁱ ⊕ (-t̃_hⁱ))/(i+1)! u_c) ⊕ Ê(t_max)x_0 ⊕ Ê(t_max)t_max u_c. | [`TrajectoryError.lean`](../../src/CORALean/HybridDynamics/Operations/TrajectoryError.lean), [`TrajectoryErrorOuter.lean`](../../src/CORALean/HybridDynamics/Theorems/TrajectoryErrorOuter.lean) — the right-hand side as CORA computes it (`LinearSys.trajectoryError`, the series cut at `η + 1`, `f₁ = f₂`): every `x(t) − y(t)` with `t ∈ [t_min, t_max]`, `0 ≤ t_min`, `x₀ ∈ ξ ⊕ Y`, `x` the solution of eq. (5) and `y` the flow of eq. (3) from the same `x₀` with `b` of `Prop. 1` at `t̃_h = tc`, lies in it. The index of the second sum starts at `1` in CORA, its `i = 0` term being `0`; outer only | `underspecified` — the right-hand side is an enclosure, not the set (cut at `η`, `Ê` for the rest), and `y` starts at the same `x₀` as `x`; see Findings |
| `Eq. 15` | R_h(x_0) = x_0 + (Ax_0 + b)(d - nᵀ(x_0 ⊕ E))/(nᵀ(Ax_0 + b)) ⊕ E encloses the states x_h hitting H, split as y_h(x_0) ⊕ R_{h,E}(x_0). | [`HitSet.lean`](../../src/CORALean/HybridDynamics/Definitions/HitSet.lean), [`MemHitSet.lean`](../../src/CORALean/HybridDynamics/Theorems/MemHitSet.lean) — in the split form; a state `x₀ + (Ax₀ + b)t + e`, `e ∈ E` (eq. 14), on `nᵀx = d` lies in it, at `nᵀ(Ax₀ + b) ≠ 0` | `correct` |
| `Prop. 2` | (Partial derivatives of y_h) With Λ(y) = nᵀ(Ay + b), Υ = nᵀA, Θ(y) = -nΛ(y) - (d - nᵀy)Υᵀ, Ω = -nΥ + Υᵀnᵀ: L_il = ∂y_{h,i}/∂x_0l = I_il + A_il(d - Σⱼ nⱼx_0j)/Λ + (Σⱼ A_ij x_0j + bᵢ)Θ_l/Λ², and ∂²y_{h,i}/∂x_0l∂x_0m = Q^(i)_lm/Λ², Q^(i)_lm = A_il Θ_m + A_im Θ_l + (Ω_lm - 2Θ_lΥ_m/Λ)(Σⱼ A_ij x_0j + bᵢ). | [`HitPoint.lean`](../../src/CORALean/HybridDynamics/Definitions/HitPoint.lean), [`HitJacobian.lean`](../../src/CORALean/HybridDynamics/Definitions/HitJacobian.lean), [`HitHessian.lean`](../../src/CORALean/HybridDynamics/Definitions/HitHessian.lean), [`HasDerivAtHitPoint.lean`](../../src/CORALean/HybridDynamics/Theorems/HasDerivAtHitPoint.lean), [`HasDerivAtHitJacobian.lean`](../../src/CORALean/HybridDynamics/Theorems/HasDerivAtHitJacobian.lean) — as partial derivatives along the axes, `L_im` differentiated along `l` for the second, wherever `Λ ≠ 0`; the printed `Θ_l(x_0)/Λ(x_0) 2Υ_m` read as `2Θ_lΥ_m/Λ`, the reading Prop. 3's `ψ_{c,l}2Υ_m` confirms | `correct` |
| `Prop. 3` | (Taylor Series of y_h) y_{h,i}(x_0) ∈ (y_{h,i}(ξ) + L_i(ξ)ν) ⊕ ½νᵀQ̃^(i)ν, ν = x_0 - ξ, Q̃^(i) = [φ̲, φ̄] ⊗ Q^(i) with [φ̲, φ̄] ⊇ {1/Λ(x_0)²} and Q^(i) enclosed by the matrix zonotope (C̃^(i), G̃^(i,1), ..., G̃^(i,1+2p)). | [`HitHessianNum.lean`](../../src/CORALean/HybridDynamics/Definitions/HitHessianNum.lean), [`HitPointMemTaylor.lean`](../../src/CORALean/HybridDynamics/Theorems/HitPointMemTaylor.lean) — (17) for x_0, ξ in a convex R(0) on which Λ ≠ 0, the remainder at a point of R(0) and a φ ∈ [φ̲, φ̄]; [`HitHessianMatZono.lean`](../../src/CORALean/HybridDynamics/Operations/HitHessianMatZono.lean), [`HitHessianNumMemHitHessianMatZono.lean`](../../src/CORALean/HybridDynamics/Theorems/HitHessianNumMemHitHessianMatZono.lean), [`HitHessianMatZonoCounterexample.lean`](../../src/CORALean/HybridDynamics/Theorems/HitHessianMatZonoCounterexample.lean) — the matrix zonotope of the proof's (18) and (19), which holds Q^(i)(x_0) when Θ/Λ lies in the one-generator zonotope ψ_c ⊕ [-1, 1]ψ_g, and the counterexample with ψ enclosed coordinate by coordinate **Counterexample:** `GuardMap.hitHessianMatZono_counterexample` | `fixed` — with (19)'s interval arithmetic each coordinate of Θ/Λ has its own factor, while G̃^(i,1) scales all of ψ_g by one: Q^(1) at x_0 = (3, 0) is outside the matrix zonotope; true when Θ/Λ ∈ ψ_c ⊕ [-1, 1]ψ_g as a vector; Λ ≠ 0 on R(0) and ξ ∈ R(0) supplied; see Findings |
| `Sec. 5.4` | R_g = y_h(ξ) ⊕ L ⊗ (R(0) ⊕ (-ξ)) ⊕ ½[φ̲, φ̄] ⊗ R_quad ⊕ R_{h,E}(R(0)), R_quad by Thm. 1, encloses the guard intersection. | [`HitEnclosure.lean`](../../src/CORALean/HybridDynamics/Definitions/HitEnclosure.lean), [`HitSetSubsetHitEnclosure.lean`](../../src/CORALean/HybridDynamics/Theorems/HitSetSubsetHitEnclosure.lean), [`HitHessianNumEqHitHessianMatZono.lean`](../../src/CORALean/HybridDynamics/Theorems/HitHessianNumEqHitHessianMatZono.lean) — `GuardMap.hitEnclosure` is `R_g` with `L = L(ξ)`, `R_quad` by `Zonotope.quadMapMatZono` from the matrix zonotopes of `Prop. 3`, `[φ̲, φ̄] ⊗ R_quad` as the paper computes it by (10) and (11), and `R_{h,E}(R(0))` the product of sets; `GuardMap.hitSet_subset_hitEnclosure`: `R_h(x₀) ⊆ R_g` (eq. 15) for every `x₀ ∈ R(0)`, given `Λ ≠ 0` on `R(0)`, `ξ ∈ R(0)`, `[φ̲, φ̄] ⊇ {1/Λ(x₀)²}` and `Θ/Λ ∈ ψ_c ⊕ [-1, 1]ψ_g` as a vector on `R(0)` | `underspecified` — holds with (19) read as one factor for the whole vector `Θ/Λ`, the reading under which `Prop. 3` holds, and with `Λ ≠ 0` on `R(0)` and `ξ ∈ R(0)`, which the formalization supplies; the printed coordinatewise derivation does not give it, an exact remainder at `ξ` with `φ = 1/(Λ(ξ)Λ(x₀))` does; see Findings |
| `Sec. 5.4 (complexity)` | The overall complexity of computing R_g is O(n⁶), set by R_quad; O(n³) when the constant flow approximation suffices. | n/a — a running time stated of the construction, which the tree can only assert (`Complexity/Time/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Sec. 6` | Powertrain with backlash, up to 101 states, against the geometric approach and SpaceEx (Tables 1-2, Figs. 5-8). | n/a — an experiment, not a claim to formalize | `not-a-claim` |

## Findings

**`Thm. 1` — whose factors.** The theorem's set is `{λ | λᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z, Q⁽ⁱ⁾ ∈ Q⁽ⁱ⁾}`,
each `Q⁽ⁱ⁾` a matrix zonotope of its own, so the coordinates may pick their matrices
independently. The proof's eq. (12) writes `λᵢ = xᵀ(D⁽ⁱ⁾ + Σⱼ βⱼK⁽ⁱ'ʲ⁾)x` with one `βⱼ` for all
`i`, and the enclosure `Z_D ⊕ ([-1, 1] ⊗ Z_K(1)) ⊕ ...` needs exactly that: `[-1, 1] ⊗ Z_K(j)`
scales all coordinates by one factor. At `n = ν = 1`, `m = 2`, `Z = {1}`, `D⁽ⁱ⁾ = 0` and
`K⁽ⁱ'¹⁾ = 1`, independent factors reach `λ = (1, -1)`, while the enclosure is the segment from
`(-1, -1)` to `(1, 1)`. Sec. 5.4 applies the theorem to the `Q⁽ⁱ⁾` of `Prop. 3`, whose remainders
sit at a Lagrange point per coordinate, so their factors are not shared there either; the
enclosure of `Sec. 5.4` holds by another route (see `Sec. 5.4` below).
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

**`Prop. 3` — one factor for `Θ/Λ`.** The matrix zonotope's first generator
`G̃^(i,1)_lm = -ψ_{g,l} 2Υ_m (∑ⱼ A_ij c_{x,j} + bᵢ)` multiplies every row `l` by the factor of
`[-1, 1]ψ_g`, so it encloses `Q⁽ⁱ⁾(x₀)` only if `Θ(x₀)/Λ(x₀) = ψ_c + κψ_g` with one `κ` for all
`l`. The proof's (19) gets `ψ_c`, `ψ_g` "using interval arithmetic", an interval per
coordinate, which does not give that. In `ℝ²` with `A = [0 0; 1 -1]`, `b = (1, 0)`, `n = (0, 1)`,
`d = 1` and `R(0) = (2, 0) + [-1, 1](1, 0)`: `Θ/Λ = (-1/Λ, 1/Λ - 1)` with `Λ ∈ [1, 3]`, enclosed
coordinatewise by `ψ_c = (-2/3, -1/3)`, `ψ_g = (1/3, 1/3)`; for `i = 1` all generators but
`G̃^(1,1)` vanish, and at `x₀ = (3, 0)` entry `(1, 1)` of `Q⁽¹⁾(x₀) = C̃ + κG̃^(1,1)` needs `κ = 1`,
entry `(2, 1)` needs `κ = -1`. Since `Θ(x₀)/Λ(x₀) = -n - τ(x₀)Υᵀ`, `τ = (d - nᵀx₀)/Λ`, an interval
`τ_c ± τ_g` of `τ` gives the one-generator form `ψ_c = -n - τ_cΥᵀ`, `ψ_g = -τ_gΥᵀ`, with which the
enclosure holds. CORA's `guardIntersect_hyperplaneMap` takes `psi_g = rad(psi_int)`, the
coordinatewise radii; [`GuardIntersectHyperplaneMap.lean`](../../src/CORALean/HybridDynamics/Operations/GuardIntersectHyperplaneMap.lean)
formalizes it with the one-generator form, and is sound with it. (17) itself needs `Λ ≠ 0` on `R(0)` and `ξ ∈ R(0)`, unstated.
[`HitHessianMatZonoCounterexample.lean`](../../src/CORALean/HybridDynamics/Theorems/HitHessianMatZonoCounterexample.lean),
[`HitHessianNumMemHitHessianMatZono.lean`](../../src/CORALean/HybridDynamics/Theorems/HitHessianNumMemHitHessianMatZono.lean),
[`HitPointMemTaylor.lean`](../../src/CORALean/HybridDynamics/Theorems/HitPointMemTaylor.lean)

**`Sec. 5.4` — an exact remainder, not the coordinatewise one.** `R_g` encloses `y_h(x₀)` for
all coordinates with one `[φ̲, φ̄] ⊗ R_quad`, `R_quad` from `Thm. 1`. The paper derives it from
`Prop. 3`, a statement per coordinate: `y_{h,i}`'s remainder is `½φᵢνᵀQ⁽ⁱ⁾(xᵢ)ν` at its own
Lagrange point `xᵢ` with its own `φᵢ = 1/Λ(xᵢ)²`, while `Thm. 1` encloses `{λ | λᵢ = xᵀQ⁽ⁱ⁾x}`
only with one factor per generator for every coordinate (`Thm. 1` above); that composition does
not establish the enclosure. It holds nonetheless, because `y_h` is a ratio with the affine
denominator `Λ`: with `ν = x₀ − ξ`,
`y_h(x₀) = y_h(ξ) + L(ξ)ν + ½φ(νᵀQ⁽ⁱ⁾(ξ)ν)ᵢ` exactly, with the one `φ = 1/(Λ(ξ)Λ(x₀))`
(`νᵀQ⁽ⁱ⁾(ξ)ν = 2(Θ(ξ)ᵀν)((Aν)ᵢ − (Υν)(Aξ + b)ᵢ/Λ(ξ))`, `Ω` being skew). `Λ` keeps its sign on
the convex `R(0)`, so `φ` is the geometric mean of `1/Λ(ξ)²` and `1/Λ(x₀)²` and lies in
`[φ̲, φ̄]`; and `Q⁽ⁱ⁾(ξ)` is the point of all the matrix zonotopes at the same factors `(κ, β, κβ)`
of `ξ` once `Θ(ξ)/Λ(ξ) = ψ_c + κψ_g` as a vector — the corrected reading of (19) from `Prop. 3`
above. Then the vector lies in `R_quad` by `Thm. 1` with shared factors, and `R_{h,E}(x₀)` lies
in `R_{h,E}(R(0))` at `a = Λ(x₀) ∈ I`. With the coordinatewise intervals of (19) the matrix
zonotopes need not contain `Q⁽ⁱ⁾(ξ)` (`Prop. 3`), and whether `R_g` still encloses `R_h(x₀)`
then is open here: no counterexample is known, and a numerical search (not in Lean) found none.
The paper's `ξ` is a point of `R(0)` and `Λ ≠ 0` on it, both unstated.
[`HitSetSubsetHitEnclosure.lean`](../../src/CORALean/HybridDynamics/Theorems/HitSetSubsetHitEnclosure.lean),
[`HitEnclosure.lean`](../../src/CORALean/HybridDynamics/Definitions/HitEnclosure.lean),
[`HitHessianNumEqHitHessianMatZono.lean`](../../src/CORALean/HybridDynamics/Theorems/HitHessianNumEqHitHessianMatZono.lean)
