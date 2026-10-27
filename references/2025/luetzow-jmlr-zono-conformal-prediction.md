# Zono-Conformal Prediction: Zonotope-Based Uncertainty Quantification for Regression and Classification Tasks

```bibtex
@article{lutzow2025zono,
  author = {Lützow, L. and Eichelbeck, M. and Kochenderfer, M. J. and Althoff, M.},
  title = {Zono-Conformal Prediction: Zonotope-Based Uncertainty Quantification for Regression and Classification Tasks},
  journal = {Journal of Machine Learning Research},
  year = {2025}
}
```

**Source:** http://jmlr.org/papers/volume26/25-1161/25-1161.pdf (the published JMLR article, CC-BY, 37 pages, read in full; text extracted with `pypdf`; volume, number and pages from the JMLR record). It matches arXiv:2508.11025v3 page for page. CORA cites the arXiv version, without result numbers, in `global/classes/@confPredictor` (`confPredictor.m`, `calibrate.m`, `predict.m`, `initializeUncertainties.m`, `evaluateData.m`, `evaluateCoverage.m`) and `contDynamics/@contDynamics/private/priv_conform_iterOD.m`, the boundary-point search for outliers.  
**Inventory:** confirmed (Definitions 1-2, Problems 1-2, Example 1, Lemmas 3-5, Theorems 6-7 and Propositions 8-10, one shared counter, equations (1)-(33), Sections 1-7 and Appendices A-B, Tables 1-3)

Zonotopic prediction sets for a point predictor `f`: uncertainties `u` inserted into `f`, linearized
at `u = 0`, give `Y_ZCP(x) = ⟨f(x), D̄(x) G_u diag(α)⟩` (`Lemma 3`), and the stretch factors `α`
are identified by one linear program whose feasible points are exactly the predictors containing
every data point (`Thm. 6`) or predicting every data point's class (`Thm. 7`), at the cost of
summed interval norms of rotated sets (`Lemma 4`). Outliers are removed by mixed-integer
programs (`Prop. 9`, `Prop. 10`) or a search over boundary points, which one more linear program
detects (`Prop. 8`): the search is formalized and proved to find the optimal removal. The
coverage guarantees are scenario theory's, cited, and not formalized; the convexity they rest on
is.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotopes, Kühn 1998) `Z = {c + Σᵢ λᵢ G₍·,ᵢ₎ \| λᵢ ∈ [-1, 1]} = ⟨c, G⟩`. | n/a — restated from Kühn 1998; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Def. 2` | (Interval norm, Althoff 2023) `‖Z‖_I = 1ᵀ\|G\|1`. | n/a — restated from Althoff 2023; tracked as `Eq. 11` on [Althoff 2023](../2023/althoff-arch-reachset-conformance.md) | `restated` |
| `Eq. 1` | (Interval predictor models, Campi et al. 2009, Problem 1) `min μr + γ` s.t. `\|y - cᵀψ̃(x)\| ≤ r‖ψ̃(x)‖₂ + γ` on the data. | n/a — restated; tracked as `Sec. 3` on [Campi, Calafiore, Garatti 2009](../2009/campi-automatica-interval-predictor-models.md) (Problem 1.a) | `restated` |
| `Eq. 2` | (Marginal coverage) `E{η(M_cal)} ≥ 1 - ε`. | n/a — the definition of the guarantee | `not-a-claim` |
| `Eq. 3` | (Split conformal prediction) `Y_CP(x) = {y \| s(x, y) ≤ q_ε}`, `q_ε` the `1 - n_out/n_m` empirical quantile of the scores, `n_out = n_m - ⌈(n_m + 1)(1 - ε)⌉` (4); scores (5), (6). | n/a — restated from Angelopoulos and Bates 2023 and the works cited with (5), (6) | `restated` |
| `Eq. 7` | (Convex scenario program) `argmin J(θ)` s.t. `g(δ, θ) ≤ 0` for the samples kept, assumed non-degenerate with a unique optimum. | n/a — a problem statement | `not-a-claim` |
| `Eq. 8` | (Rocchetta et al. 2021, Thm. 3) `P{η ≥ 1 - ε} ≥ 1 - C(n_out + n_θ - 1, n_out) Σ_{i < n_out + n_θ} C(n_m, i) εⁱ(1 - ε)^{n_m - i}`. | n/a — restated from Rocchetta et al. 2021 | `restated` |
| `Eq. 9` | (O'Sullivan et al. 2025) `E{η} ≥ 1 - C(n_out + n_θ - 1, n_out)(n_out + n_θ)/(n_m + 1)`. | n/a — restated from O'Sullivan et al. 2025 | `restated` |
| `Sec. 2.3` | (9) reduces to (2) whenever `ε ≥ C(n_out + n_θ - 1, n_out)(n_out + n_θ)/(n_m + 1)`, which holds for conformal predictors with `n_θ = 1` and `n_out` as in (4). | [`CpScenarioTermLe.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/CpScenarioTermLe.lean) — `cp_scenario_term_le`, for `n_out ≥ 0` | `correct` |
| `Problem 1` | (Uncertainty quantification for regression) `min Σ size(Y_ZCP(x_eval⁽ᵐ⁾))` (10a) s.t. `y⁽ᵐ⁾ ∈ Y_ZCP(x⁽ᵐ⁾)` (10b). | n/a — a problem statement | `not-a-claim` |
| `Eq. 11` | `classes(Y) = {i \| ∃y ∈ Y: y₍ᵢ₎ = maxⱼ y₍ⱼ₎}`, `classes(y)` likewise. | [`ZonoConformal.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/ZonoConformal.lean) — `classesSet`, `classesVec` | `correct` |
| `Problem 2` | (Uncertainty quantification for classification) (12a) s.t. `classes(y⁽ᵐ⁾) ⊆ classes(Y_ZCP(x⁽ᵐ⁾))` (12b). | n/a — a problem statement | `not-a-claim` |
| `Eq. 13` | (Zono-conformal predictor) `Y_ZCP(x) = {f(x) + D̄(x)u \| u ∈ U}`, `D̄(x) = ∇_u f̃(x, u)\|_{u=0}`. | [`ZonoConformal.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/ZonoConformal.lean) — `zcpSet`, `D̄(x)` given | `correct` |
| `Example 1` | Output and parametric uncertainties inserted into `f(x) = (3x₁ + x₂, 2x₂³)`. | n/a — an illustration | `not-a-claim` |
| `Sec. 4.2` | (Uncertainty placement) All output uncertainties, the rest sampled at random from the parametric ones. | n/a — a heuristic, compared experimentally in Sec. B.1 | `not-a-claim` |
| `Eq. 14` | (Cost) `size(Y_ZCP(x)) = Σ_{i=0}^{n_r} ‖Rᵢ Y_ZCP(x)‖_I`, `Rᵢ` random orthogonal, `R₀ = I`. | n/a — the definition of the cost; `Thm. 6` and `Thm. 7` take any `Rᵢ` | `not-a-claim` |
| `Eq. 15` | (Uncertainty set) `U = ⟨0, G_u diag(α)⟩`, `α ≥ 0`, `G_u` user-defined. | n/a — the template, `templateZono` in `zcpSet` | `not-a-claim` |
| `Lemma 3` | With (15), `Y_ZCP(x) = ⟨f(x), D̄(x) G_u diag(α)⟩` (16). | [`ZcpSetEq.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ZcpSetEq.lean) — `zcpSet_eq`, an equality of sets | `correct` |
| `Lemma 4` | `‖Rᵢ Y_ZCP(x)‖_I = 1ᵀ\|Rᵢ D̄(x) G_u\|α` (17). | [`ZcpIntervalNorm.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ZcpIntervalNorm.lean) — `intervalNorm_zcpSet`: `Rᵢ Y_ZCP(x)` is the zonotope with generators `αⱼ Rᵢ D̄ G_u,ⱼ`, whose interval norm is (17) for `α ≥ 0` | `correct` |
| `Lemma 5` | `y ∈ Y_ZCP(x)` iff `∃β̄: \|β̄\| ≤ α, y = f(x) + D̄(x) G_u β̄` (18). | [`MemZcpSetIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemZcpSetIff.lean), [`MemTemplateZonoIffGen.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemTemplateZonoIffGen.lean) — `mem_zcpSet_iff`, `α ≥ 0` | `correct` |
| `Thm. 6` | (Zono-conformal regression) Problem 1 with the cost (14) can be solved with (13), (15), `α` from the linear program `min Σₘ Σᵢ 1ᵀ\|Rᵢ D̄(x_eval⁽ᵐ⁾) G_u\|α` (19a) s.t. `0 ≤ α` (19b), `0 ≤ α ± βₘ` (19c), (19d), `y_Δ⁽ᵐ⁾ = D̄(x⁽ᵐ⁾) G_u βₘ` (19e). | [`ZcpRegressionLp.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ZcpRegressionLp.lean) — `zcp_regression_lp`: for `α ≥ 0`, (19c)-(19e) are solvable iff (10b) holds, and (19a) is (10a); so the program's optimum is Problem 1's over the predictors (13), (15) | `correct` |
| `Thm. 7` | (Zono-conformal classification) Problem 2 with the cost (14) can be solved with (13), (15), `α` from (20): (19a)-(19d) with `-Tₘ f(x⁽ᵐ⁾) ≤ Tₘ D̄(x⁽ᵐ⁾) G_u βₘ` (20e), `Tₘ = vert(e_{classes(y⁽ᵐ⁾)}ᵀ) - I` (21), each output one-hot (22). | [`ZcpClassificationLp.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ZcpClassificationLp.lean), [`ClassesVecSingleSubsetIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ClassesVecSingleSubsetIff.lean) — `zcp_classification_lp`, one class per data point as (22) assumes | `correct` |
| `Eq. 21` | `Tₘ = vert_{n_y}(e_{classes(y⁽ᵐ⁾)}ᵀ) - I`. | [`ZonoConformal.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/ZonoConformal.lean) — `classMat` | `correct` |
| `Sec. 5.1.1` | (Search over boundary points) A point is a boundary point if an infinitesimal reduction of some `α₍ⱼ₎` loses it; a search tree removing one boundary point of its parent per child, `n_out` layers deep: the leaf with the lowest objective identifies the optimal set of outliers. | [`SearchOutliersOptimal.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/SearchOutliersOptimal.lean), [`SearchOutliers.lean`](../../src/CORALean/ContDynamics/Conform/Operations/SearchOutliers.lean) — `searchOutliers_optimal`: the least leaf cost is the least cost over all removals of at most `n_out` points, and one attains it | `correct` |
| `Prop. 8` | (Detection of boundary points) With `α*` optimal for (19) or (20), the linear program `argmin -1ᵀδ` s.t. `0 ≤ δ₍ₘ₎`, `-α* ≤ ±βₘ - f δ₍ₘ₎`, (19e) or (20e), `f₍ⱼ₎ = 1` iff `α*₍ⱼ₎ > 0` (23): the `m`-th point is a boundary point iff `δ₍ₘ₎ = 0`. | [`ZcpBoundaryLp.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ZcpBoundaryLp.lean), [`NotIsBoundaryPointIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/NotIsBoundaryPointIff.lean) — `isBoundaryPoint_iff_lp23`, at any optimal solution of (23); (24) is `not_isBoundaryPoint_iff` | `underspecified` — at `α* = 0` (23) is unbounded and has no solution to read `δ` from; see Findings |
| `Sec. 5.1.2` | (Greedy search) Keep only the cheapest child per level. | n/a — a heuristic, "trading optimality guarantees" | `not-a-claim` |
| `Prop. 9` | (Regression with outlier removal) With (19e) replaced by `0 = D̄ G_u βₘ - y_Δ⁽ᵐ⁾ρ₍ₘ₎` (25a), `n_m - n_out ≤ 1ᵀρ` (25b), `ρ ∈ {0, 1}ⁿᵐ` (25c), Problem 1 with at most `n_out` points violating (10b) can be solved with `Thm. 6`. | [`ZcpRegressionMilp.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ZcpRegressionMilp.lean) — `zcp_regression_milp`: feasible iff all but at most `n_out` points meet (10b) | `correct` |
| `Prop. 10` | (Classification with outlier removal) With (20e) replaced by `0 ≤ Tₘ D̄ G_u βₘ + Tₘ f(x⁽ᵐ⁾)ρ₍ₘ₎` (26a), (26b), (26c), likewise for Problem 2 and `Thm. 7`. | [`ZcpClassificationMilp.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ZcpClassificationMilp.lean) — `zcp_classification_milp` | `correct` |
| `Sec. 5.2` | (Coverage guarantees) With the data independent and identically distributed and independent of the evaluation points, (19) and (20) are convex scenario programs, so the coverage of zono-conformal predictors satisfies (8) and (9). | n/a — the bounds are (8) and (9), restated from Rocchetta et al. 2021 and O'Sullivan et al. 2025, whose non-degeneracy and unique-optimum assumptions the paper takes for (19) and (20); scenario theory is not in Mathlib. That each point's constraint is convex in `α` is `convex_fitsUnder` | `restated` |
| `Sec. 6` | Experiments: regression (Tables 1-2, Figs. 2-3) and classification (Figs. 4-5) against CPs and IPMs. | n/a — experiments | `not-a-claim` |
| `Eq. 29` | (Gover and Krikorian 2010, Cor. 3.4) The volume of `⟨c, G⟩` is `2ⁿ Σ \|det(G_{j₁,…,jₙ})\|`. | n/a — restated from Gover and Krikorian 2010 | `restated` |
| `Sec. B` | Ablations: placement strategies (QR, random), cost functions (30)-(33), outlier detection methods (Figs. 6-9, Table 3). | n/a — experiments | `not-a-claim` |

## Findings

**`Prop. 8` — when (23) has a solution.** The proposition reads `δ` off "the" optimal solution of
(23). If `α* = 0`, which (19) returns when every data point is predicted exactly, `f = 0` and
the constraints on `δ₍ₘ₎` are `δ₍ₘ₎ ≥ 0` alone: (23) is unbounded and there is no `δ` to read.
The statement is then vacuous, and there are no boundary points either, since no `α₍ⱼ₎ > 0` can
be reduced. Whenever (23) has an optimal solution the equivalence holds
(`isBoundaryPoint_iff_lp23`): the blocks `(βₘ, δₘ)` are independent, so each `δ₍ₘ₎` is at its
largest, and that is positive iff one `βₘ` fits strictly under every `α*₍ⱼ₎ > 0`, (24). The
proof's "this occurs if there exists a vector `βₘ` … (24)" needs the reverse too: one
reduction per coordinate gives one `β` per coordinate, and only because each point's
constraint is convex does their average fit strictly in all at once
(`not_isBoundaryPoint_iff`). CORA's `priv_conform_white` (`aux_determineActiveMeas`) returns
before solving (23) when the identified parameters are all `0`, and bounds each `δ₍ₘ₎` above by
the least positive `α*₍ⱼ₎`, so its program always has a solution.
[`ZcpBoundaryLp.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ZcpBoundaryLp.lean)
