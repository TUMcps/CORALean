# Checking and Establishing Reachset Conformance in CORA 2023

M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of the 10th International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.

**Source:** https://mediatum.ub.tum.de/doc/1731062/1731062.pdf (the EPiC PDF, 25 pages, pp. 9-33, read in full; text extracted with `pypdf`; the same paper as https://easychair.org/publications/paper/Zmbv, doi:10.29007/5v1g). CORA cites it in `@linearSysDT/confSynth_dyn.m`, `isconform_dyn.m` and `confSynth_gray.m` without result numbers; `confSynth_dyn` implements Thms. 1-2 (`'interval'`, `'frob'`).  
**Inventory:** confirmed (Theorems 1-2, Figures 1-8, Tables 1-4, equations (1)-(37), of which (28)-(37) are in the proofs of Appendices A-B; the rows below are the results, the numbered displays that make a claim, and the claims of Secs. 1.1-2.2 stated in prose)

The tool paper of CORA's `conform`: reachset conformance — every measurement inside the
model's reachable outputs — checked on test cases, and established by identifying stretched
zonotope templates for the initial set, the disturbance and the noise with a linear or a
quadratic program. Everything about linear models is formalized: subtracting the nominal
run (`Eq. 5`, `Eq. 8`), the program's constraints exactly the conformant parameters and its
objectives exactly the costs (`Thm. 1`, `Thm. 2`), measurement errors (`Sec. 2`). Three
printed claims fail: the one-step recursion (7) for the continuous-time inner approximation,
the falsification test `y ∉ R ⊕ V` for asymmetric `V` (`Sec. 2.2`), and the capsule test
of `Table 2`, which misses the boundary. None of them reaches CORA.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 1.1` | Conformance relations from the survey [58]: `S_I conf S_A ∧ S_A ⊨ spec ⇒ S_I ⊨ spec`; trace conformance, simulation relations (a simulation implies trace conformance [15, Thm. 7.70]); reachset conformance `∀t ∀u: Reach_t(S_I, u) ⊆ Reach_t(S_A, u)`, necessary and sufficient to transfer safety [59, Thm. 1], and implied by trace conformance [59, Thm. 2]. | n/a — restated from Roehm et al. 2019 [58] and Roehm, Rausch and Althoff 2022 [59] | `restated` |
| `Sec. 2` | With measurement errors `V`, a measurement `y` falsifies conformance for sure only if `y ⊕ V` misses the reachable set, and the exact output is certainly reachable if `y ⊕ V` lies in it; so an outer approximation falsifies and an inner one certifies (Fig. 2). | [`MeasurementConformance.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MeasurementConformance.lean) — over any additive group | `correct` |
| `Table 1` | The implemented test-generation methods (`constrained`, `gaussian`, `rrt`, `standard`). | n/a — a list of tool features | `not-a-claim` |
| `Sec. 2.1` | The `testCase` class and `sequentialTestCases`, giving `y⁽ᵐ⁺¹⁾(t_k) = y⁽ᵐ⁾(t_{k+1})`. | n/a — a description of the tool's interface | `not-a-claim` |
| `Sec. 2.2` | `R ⊖ V = {x \| x ⊕ V ⊆ R}`; measurement conformance is `y ∈ R ⊖ V`, falsification `y ∉ R ⊕ V`. | [`DisjointSingletonAddIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/DisjointSingletonAddIff.lean), [`FalsifyAddCounterexample.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/FalsifyAddCounterexample.lean) — `y ⊕ V` misses `R` iff `y ∉ R ⊕ (-V)`; the counterexample **Counterexample:** `Conform.falsify_add_counterexample` | `fixed` — the falsification test is `y ∉ R ⊕ (-V)`: at `R = {0}`, `V = [0, 1]`, `y = -1`, `y ⊕ V` meets `R` yet `y ∉ R ⊕ V`; the two agree for `V = -V`; see Findings |
| `Sec. 2.2 (zonotopes)` | Zonotopes in up to 4 dimensions are converted to halfspaces [11, Thm. 7], larger ones checked by [39, eq. (8)]; a point is in a zonotope bundle iff in every zonotope [10, Def. 4]; in a constrained zonotope iff the linear program [62, eq. (20)] finds `‖β‖∞ ≤ 1`. | n/a — restated from Althoff, Stursberg and Buss 2010 [11], tracked as `Thm. 7` on [Althoff, Stursberg, Buss 2010](../2010/althoff-nahs-zonotopes-polytopes.md); Kulmburg and Althoff 2021 [39]; Althoff and Krogh 2011 [10]; Scott et al. 2016 [62] | `restated` |
| `Table 2` | Point containment checks: capsule `(‖(δᵀg_n)g_n - δ‖₂ < r ∧ \|δᵀg_n\| < ‖g‖₂) ∨ ‖δ - g‖₂ ≤ r ∨ ‖δ + g‖₂ ≤ r` with `g_n = g/‖g‖₂`, `δ = x - c`; ellipsoid `xᵀQx ≤ 1`; H-polytope `Cx ≤ d`; interval `x̲ ≤ x ≤ x̄`; level set `µ(x) ≤ 0` — exact containment checks. | [`ContainsTableCounterexample.lean`](../../src/CORALean/ContSet/Capsule/Real/Theorems/ContainsTableCounterexample.lean), [`ContainsTableIff.lean`](../../src/CORALean/ContSet/Capsule/Real/Theorems/ContainsTableIff.lean) — the capsule row; the other four restate their sets' definitions **Counterexample:** `Capsule.contains_table_counterexample` | `fixed` — the capsule's axis test `< r` rejects points at distance exactly `r` from the axis: `c = 0`, `g = (1, 0)`, `r = 1`, `x = (0, 1)` is in the capsule and fails all three disjuncts; with `≤ r` the test is exact; see Findings |
| `Eq. 1` | The model `ẋ = A x + B u + w`, `y = C x + v`. | n/a — the model's definition; its discrete-time counterpart is the subject of `Sec. 3` | `not-a-claim` |
| `Eq. 2` | The exact reachable set `e^{At}(x₀ ⊕ X̃₀) ⊕ ∫₀ᵗ e^{A(t-τ)}(B u(τ) ⊕ W_c) dτ` contains its inner approximation with constant disturbance, `R_x(t) = e^{At}(x₀ ⊕ X̃₀) ⊕ ∫ e^{A(t-τ)} B u dτ ⊕ ∫ e^{A(t-τ)} dτ W_c` [43, Prop. 1]. | n/a — restated from Liu and Althoff 2018 [43, Prop. 1] | `restated` |
| `Eq. 3` | `R(t, x₀, u) = C R_x(t, x₀, u) ⊕ V`. | n/a — a definition, formalized inside `Eq. 5`'s statement | `not-a-claim` |
| `Eq. 4` | Reachset conformance at `h`: `∀y(h) ∈ Y(h): y(h) ∈ R(h, x₀, u)`. | n/a — a definition, formalized inside `Eq. 5`'s statement | `not-a-claim` |
| `Eq. 5` | By (2)-(3), `y(h) ∈ R(h)` iff `y(h) - ỹ(h) ∈ C(e^{Ah} X̃₀ ⊕ ∫₀ʰ e^{A(h-τ)} dτ W_c) ⊕ V`, independent of `x₀` and `u`. | [`MemUnderApproxIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemUnderApproxIff.lean) — for any matrices in place of `e^{Ah}` and `Υ`, and any vector in place of the input integral: only linearity is used | `correct` |
| `Eq. 6` | The notation `A_d = e^{Ah}`, `Υ = ∫₀ʰ e^{A(h-τ)} dτ`, `B_d = Υ B`, `W = Υ W_c`, `Λ_k = C A_dᵏ`. | n/a — notation | `not-a-claim` |
| `Eq. 7` | `R_x(t_{k+1}) - x̃(t_{k+1}) = A_d (R_x(t_k) - x̃(t_k)) ⊕ W`, so that `R_x(t_k) - x̃(t_k) = A_dᵏ X̃₀ ⊕ ⨁_{i<k} A_dⁱ W`. | [`UnderApproxStepNe.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/UnderApproxStepNe.lean), [`MemReachOutIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemReachOutIff.lean) — the counterexample for (2)'s set; for the model whose disturbance is drawn afresh at each step the closed form holds exactly **Counterexample:** `Conform.underApprox_step_ne` **Counterexample:** `Conform.underApprox_step_ne` | `fixed` — false for (2)'s inner approximation, whose disturbance is one constant on `[0, t]`: at `A = [0 1; 0 0]`, `h = 1`, `k = 1`, `X̃₀ = {0}`, `W_c = {0} × [-1, 1]` the left side is a segment and the right a parallelogram; it holds with the disturbance constant per step, the set the rest of the paper uses; see Findings |
| `Eq. 8` | For every `t_k`: `y(t_k) - ỹ(t_k) ∈ Λ_k X̃₀ ⊕ ⨁_{i<k} Λᵢ W ⊕ V`. | [`MemReachOutIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemReachOutIff.lean), [`DevSet.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/DevSet.lean) — equivalent to `y(t_k) ∈ R(t_k)` for the discrete-time model | `underspecified` — exact for the discrete-time model (`Sec. 3`), and for the continuous one with the disturbance held constant per step; for (2)'s set it is reached through (7), which fails there (`Eq. 7`) |
| `Sec. 3` | The constraint (8) is the same for the discrete-time system `x(t_{k+1}) = A_d x(t_k) + B_d u(t_k) + w(t_k)`, `w ∈ W`, under zero-order hold, so the results transfer to it. | [`MemReachOutIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemReachOutIff.lean) — `y ∈ R(k)` iff `y - ỹ(k)` is in the deviation set, for the discrete-time model | `correct` |
| `Sec. 3 (W_c)` | `W_c = (∫₀ʰ e^{A(h-τ)} dτ)⁻¹ W = (A⁻¹(e^{Ah} - I))⁻¹ W` [3, eq. (3.6)]; considering all disturbances only adds conservatism. | n/a — restated from Althoff 2010 [3, eq. (3.6)] | `restated` |
| `Eq. 9` | The templates `X̃₀ = ⟨c_X, G_X diag(α_X)⟩`, `W = ⟨c_W, G_W diag(α_W)⟩`, `V = ⟨c_V, G_V diag(α_V)⟩`. | [`TemplateZono.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/TemplateZono.lean) | `correct` |
| `Eq. 10` | `c = [c_X; c_W; c_V]`, `α = [α_X; α_W; α_V]`. | n/a — notation | `not-a-claim` |
| `Eq. 11` | The interval norm `‖Z‖_{Ĩ,σ} = σᵀ\|[c, G]\| 1`, `σ > 0`, with a) `≥ 0`, b) `‖⟨0⟩‖ = 0`, c) `‖γZ‖ = \|γ\| ‖Z‖`, d) `‖⟨[c₁, G₁] + [c₂, G₂]⟩‖ ≤ ‖⟨[c, G₁]⟩‖ + ‖⟨[c₂, G₂]⟩‖`; without the centre, `‖Z‖_{I,σ} = σᵀ\|G\| 1` (11). | [`IntervalNormProps.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/IntervalNormProps.lean), [`IntervalNorm.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/IntervalNorm.lean) — a)-d) for `σᵀ\|M\|1` as a function of the matrix, `σ ≥ 0` | `underspecified` — d)'s first right-hand term prints `c` for `c₁` |
| `Thm. 1` | (Linear program) `min nᵀz s.t. Ãz ≤ b̃` (12)-(21) minimizes `Σ_k ω_k ‖R(t_k) - ỹ(t_k)‖_{I,σ}` (13) and ensures reachset conformance, (8) at every `k`; `N(t_k)` the normals of the zonotope with generators `G(t_k)` (21) by [11, Thm. 7]. | [`ConformantIffLp.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ConformantIffLp.lean), [`LpCostEq.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/LpCostEq.lean), [`DevSetTemplateZono.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/DevSetTemplateZono.lean) — a point with `α ≥ 0` meets the constraints iff the model is conformant (both directions), and `nᵀz` is the cost; the minimizer the solver returns is the solver's | `proof-gap` — the proof takes `N(t_k)` independent of `α`, citing [46, Thm. 1], whose argument needs `α > 0`; the program allows `αᵢ = 0`, where a generator and its normals vanish. The statement holds there, with the template's normals; the template must span the output space; see Findings |
| `Eq. 22` | The Frobenius norm `‖Z‖_{F,P} = √trace(Gᵀ P G)`. | [`IntervalNorm.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/IntervalNorm.lean) — `frobNormSq`, its square | `correct` |
| `Thm. 2` | (Quadratic program) `min ½ zᵀHz s.t. Ãz ≤ b̃` with `H` from (24)-(26) minimizes `Σ_k ω_k ‖R(t_k) - ỹ(t_k)‖²_{F,P}` (23) and ensures conformance. | [`QpCostEq.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/QpCostEq.lean) — `zᵀHz` is the cost (`½` halves it, the minimizers are the same); the constraints are `Thm. 1`'s | `correct` |
| `Sec. 3.3` | For nonlinear systems: axis-aligned sets, relinearization per step, binary search per dimension. | n/a — a sketch of a heuristic, not a claim | `not-a-claim` |
| `Sec. 4` | Four use cases: analog circuit, BMW 320i, pedestrians, Schunk robot (Figs. 3-8, Tables 3-4, Eq. (27)). | n/a — experiments | `not-a-claim` |

## Findings

**`Sec. 2.2` — the falsification test needs `-V`.** A measurement `y` with error set `V` is
falsifying when `(y ⊕ V) ∩ R = ∅`, i.e. no `v ∈ V` has `y + v ∈ R`, i.e. `y ∉ R ⊕ (-V)`. The
paper checks `y ∉ R ⊕ V`, which differs for an asymmetric `V`: at `R = {0}`, `V = [0, 1]`,
`y = -1`, the exact output `y + 1 = 0` may well be reachable, yet `-1 ∉ [0, 1]` reports a
falsification. For centrally symmetric `V` — the zero-centred sets CORA's examples use — the
two coincide.
[`FalsifyAddCounterexample.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/FalsifyAddCounterexample.lean),
[`DisjointSingletonAddIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/DisjointSingletonAddIff.lean)

**`Table 2` — the capsule test misses the boundary.** The test is presented among the exact
containment checks, but its axis disjunct compares `< r`: a point at distance exactly `r`
from the open axis is in the capsule and rejected — `c = 0`, `g = (1, 0)`, `r = 1`,
`x = (0, 1)` fails the axis test (`1 < 1`) and lies `√2` from both end centres. With `≤ r` the
disjunction is exact. CORA's `capsule/contains_` compares `dist < r | withinTol(dist, r)` and
is not affected.
[`ContainsTableCounterexample.lean`](../../src/CORALean/ContSet/Capsule/Real/Theorems/ContainsTableCounterexample.lean),
[`ContainsTableIff.lean`](../../src/CORALean/ContSet/Capsule/Real/Theorems/ContainsTableIff.lean)

**`Eq. 7` — one constant disturbance is not one per step.** (2)'s inner approximation keeps
the disturbance constant on all of `[0, t]`, so `R_x(t) - x̃(t) = e^{At} X̃₀ ⊕ Υ(t) W_c` with
`Υ(t) w = ∫₀ᵗ e^{A(t-τ)} w dτ`. Since `Υ(t + h) = e^{Ah} Υ(t) + Υ(h)`, the left side of (7) is
`{(e^{Ah} Υ(t_k) + Υ(h)) w}` and the right side `e^{Ah} Υ(t_k) W_c ⊕ Υ(h) W_c`, a larger set
whenever the two images point different ways. For the nilpotent `A = [0 1; 0 0]`, `h = 1`,
`W_c = {0} × [-1, 1]`: the left side at `t₂` is the segment `{s (2, 2)}`, the right side
contains `(3/2, 1) + (-1/2, -1) = (1, 0)`. Iterated, the right side is the reachable set
under disturbances constant on each step — between (2)'s set and the exact one — which is
what (8), `Thm. 1` and the discrete-time model use; conformance established against it is
still conformance of the continuous model, so the error does not propagate to CORA.
[`UnderApproxStepNe.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/UnderApproxStepNe.lean)

**`Thm. 1` — normals at a vanished generator.** The constraint rows need normals fixed before
`α` is known; the proof takes those of `G(t_k)` and calls them independent of `α`, citing
[46, Thm. 1] — whose argument cancels `det(diag(α))` and holds for `α > 0` only. The
program's last block, `-α ≤ 0`, admits `αᵢ = 0`, where the generator vanishes and every
cross product through it is zero. The theorem survives: the template's normals at offsets
`|N G|α` still describe `⟨c, G diag(α)⟩` for all `α ≥ 0` (the point is in every stretch
`α + ε`, which shrink onto the closed zonotope). The template has to span the output space
for [11, Thm. 7] to apply; CORA's `confSynth_dyn` computes `N` from the template, as here.
[`MemScaleIff.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/MemScaleIff.lean),
[`ConformantIffLp.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ConformantIffLp.lean)
