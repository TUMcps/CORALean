# Robust Identification of Hybrid Automata from Noisy Data

N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.

**Source:** https://opus4.kobv.de/opus4-haw/files/6120/3716863.3718030.pdf (the published ACM version, open access under CC-BY, doi:10.1145/3716863.3718030, as deposited in the OPUS repository; 11 pages, read in full; text extracted with `pypdf`; the ACM Digital Library refused automated download). CORA cites the paper in `hybridDynamics/@hybridAutomaton/identify.m` and its private `priv_identify_clustering.m` (Eq. (6) in `aux_dynamicModeDecomposition`), `priv_identify_decisionTreeLearning.m` and `priv_identify_decisionTree2automaton.m` (Eq. (17), Proposition 1).  
**Inventory:** confirmed (Definitions 1-3, Algorithm 1, Proposition 1, Theorem 1, each with its own counter; equations (1)-(18); Sections 1-6; Tables 1-3)

Hybrid automata identified from noisy trajectories in three steps: local dynamics `ẋ = Aφ(x, u)`
fitted by least squares on a window of `2w + 1` points and clustered (Sec. 3.1), a decision
tree of hyperplane splits learned from a library of switching, bouncing and jumping surfaces
with a trajectory-aware Gini index (Sec. 3.2), and the tree turned into an automaton whose
guards keep resets inside the target invariants (`Prop. 1`), so that it is executable
(`Thm. 1`). Formalized: the least-squares formulas (`Eq. 5` with its Gram matrix on the wrong
side, `Eq. 6`), the window bound, `Prop. 1` and `Thm. 1` as its proof sketch argues it. The
clustering, RANSAC, gradient descent and tree learning are heuristics and searches.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Hybrid automaton) `H = ⟨F, Y, T⟩_A`: flow functions, invariants, transitions `⟨Gᵢ, rᵢ, sᵢ, zᵢ⟩_T`; urgent transitions. | n/a — a definition, after Henzinger [19]; CORALean's is `HybridAutomaton` | `not-a-claim` |
| `Def. 2` | (Polytope) `⟨C, d⟩_P = {x \| Cx ≤ d}`. | [`IdentPolytope.lean`](../../src/CORALean/HybridDynamics/Operations/IdentPolytope.lean) — `polytope`, the H-polytope of the rows | `correct` |
| `Def. 3` | (Constrained hyperplane) `⟨a, b, C, d⟩_H = {x \| aᵀx = b ∧ Cx ≤ d}`. | [`IdentHA.lean`](../../src/CORALean/HybridDynamics/Definitions/IdentHA.lean) — `conHyperplane` | `correct` |
| `Eq. 1` | Affine resets `rᵢ(x) = Hᵢx + kᵢ`. | n/a — a modelling choice | `not-a-claim` |
| `Eq. 2` | Flows `ẋ = Aᵢφ(x, u)` over a library `φ` of template functions. | n/a — a modelling choice | `not-a-claim` |
| `Eq. 3` | `ẋ(tᵢ) ≈ (x(tᵢ₊₁) - x(tᵢ₋₁))/(tᵢ₊₁ - tᵢ₋₁)`. | n/a — a numerical approximation | `not-a-claim` |
| `Eq. 4` | `min_A Σ_{i=j-w}^{j+w} ‖ẋ(tᵢ) - Aφ(x(tᵢ), u(tᵢ))‖²`. | n/a — a problem statement; its solutions are `Eq. 5` and `Eq. 6` | `not-a-claim` |
| `Eq. 5` | The optimum of (4) is `A = Ẋ(ΦᵀΦ)⁻¹Φᵀ` [42, Eq. 2.4], `Ẋ` and `Φ` with one column per data point. | [`GramTransposeSingular.lean`](../../src/CORALean/Global/GramTransposeSingular.lean), [`PinvLeastSquares.lean`](../../src/CORALean/Global/PinvLeastSquares.lean) — `det_transpose_mul_self_eq_zero`; corrected, `pinv_leastSquares` **Counterexample:** `det_transpose_mul_self_eq_zero` **Counterexample:** `det_transpose_mul_self_eq_zero` | `fixed` — with data in columns `ΦᵀΦ` is `(2w + 1) × (2w + 1)` of rank at most `v`, singular once `2w + 1 > v`; the solution is `ẊΦᵀ(ΦΦᵀ)⁻¹`; see Findings |
| `Eq. 6` | Equivalently `A = ẊVΣ⁻¹Uᵀ` with `Φ = UΣVᵀ` [42, Eq. 2.7]; rank adaption keeps the largest singular values. | [`DmdCandidateLeastSquares.lean`](../../src/CORALean/Global/DmdCandidateLeastSquares.lean) — `dmdCandidate_leastSquares`: with the economy SVD, `ẊVΣ⁻¹Uᵀ` minimizes (4) for any `Φ` | `correct` |
| `Sec. 3.1` | A lower bound for `w` is `⌈0.5(v - 1)⌉`, since at least `v` data points are needed to identify `A ∈ ℝⁿˣᵛ` uniquely; the grid for `w` and `ρ` is searched for the smallest error. | [`LeastSquaresUniqueLe.lean`](../../src/CORALean/Global/LeastSquaresUniqueLe.lean) — `le_of_leastSquares_unique`: a unique minimizer of (4) needs `2w + 1 ≥ v`, which is `w ≥ ⌈(v - 1)/2⌉`; the grid search is a heuristic | `correct` |
| `Eq. 7` | The prediction error `ε = maxᵢ ‖x(tᵢ) - x_pred(tᵢ)‖₂` on the window. | n/a — a definition | `not-a-claim` |
| `Eq. 8` | Clusters are added until the relative improvement `(εᵢ₋₁ - εᵢ)/(0.5(εᵢ + εᵢ₋₁)) ≤ τ`. | n/a — a stopping heuristic | `not-a-claim` |
| `Alg. 1` | (Library of potential partitions) Per pair of modes, a jumping surface by RANSAC (9) where jumps occur, else the better of a switching surface by gradient descent (13) and a bouncing surface by RANSAC (10). | n/a — randomized and gradient-based searches, a subject CORALean does not cover | `not-covered` |
| `Eq. 9` | (Jumping surface) `max_{a,b} \|S ∩ J ∩ F\|`, `F` the points within `ε` of the hyperplane. | n/a — an optimization problem, solved by RANSAC | `not-a-claim` |
| `Eq. 10` | (Bouncing surface) `min_{a,b} N_bounce(a, b)`. | n/a — an optimization problem, solved by RANSAC | `not-a-claim` |
| `Eq. 11` | (Switching surface) `N_switch`, the misclassified points of the two modes. | n/a — a definition | `not-a-claim` |
| `Eq. 12` | `step(aᵀx - b) ≈ 1/(1 + e^{-aᵀx+b})`. | n/a — a smoothing | `not-a-claim` |
| `Eq. 13` | The smoothed (11), minimized by gradient descent. | n/a — an optimization problem | `not-a-claim` |
| `Eq. 14` | (Gini impurity index [33, Ch. 6.3.1]) `1 - Σⱼ (\|Sⱼ\| / Σₗ \|Sₗ\|)²`, `Sⱼ` (15) the points of mode `j`. | n/a — restated from [33] | `restated` |
| `Eq. 16` | (Modified Gini index) The Gini index per connected trajectory segment, averaged weighted by length; the stopping criterion `Gini_mod < λ` and, with the count of mode changes near a surface, the selection criterion. | n/a — a definition and a heuristic | `not-a-claim` |
| `Sec. 3.3` | Each leaf of the tree corresponds to a region of a state-space partition, a polytope combining the inequalities on its path; these are the invariants. | [`SplitTreeRegions.lean`](../../src/CORALean/HybridDynamics/Operations/SplitTreeRegions.lean) — `regions`; that they cover `ℝⁿ` is the first part of `SplitTree.executable` | `correct` |
| `Eq. 17` | (Reset) `min_{H,k} Σ_{i∈J} ‖x(tᵢ₊₁) - [H, k][x(tᵢ); 1]‖²`, solved via (6) with rank adaption by cross-validation. | [`DmdCandidateLeastSquares.lean`](../../src/CORALean/Global/DmdCandidateLeastSquares.lean) — `dmdCandidate_leastSquares` at `φ(x) = [x; 1]` | `correct` |
| `Prop. 1` | For a surface `H = ⟨a, b, [], []⟩_H`, reset `r(x) = Hx + k` and target invariant `Y = ⟨C, d⟩_P`, the guard `G = ⟨a, b, CH, d - Ck⟩_H` guarantees that all states entering it are mapped into `Y`. | [`IdentGuardMapsInto.lean`](../../src/CORALean/HybridDynamics/Theorems/IdentGuardMapsInto.lean), [`IdentGuardEq.lean`](../../src/CORALean/HybridDynamics/Theorems/IdentGuardEq.lean), [`IdentGuard.lean`](../../src/CORALean/HybridDynamics/Operations/IdentGuard.lean) — `identGuard_maps_into`: every `x ∈ G` has `r(x) ∈ Y`, with `Y` an `HPolytope`; and `conHyperplane_identGuard`: `G = {x ∈ H \| r(x) ∈ Y}` | `correct` |
| `Thm. 1` | The output of the approach is a hybrid automaton guaranteed to be executable for all initial states `x(t₀) ∈ ℝⁿ` and all input signals. | [`SplitTreeExecutable.lean`](../../src/CORALean/HybridDynamics/Theorems/SplitTreeExecutable.lean) — `SplitTree.executable`: the invariants cover `ℝⁿ`, every boundary point of an invariant is in a guard leaving it (built by `Prop. 1`), every guard maps into its target | `underspecified` — "executable" is not defined; formalized as the three properties of the proof sketch, for transitions across every surface of a leaf to every leaf; see Findings |
| `Eq. 18` | The relative error `ε_rel`, dynamic-time-warping distance over the norm of the true trajectory. | n/a — an evaluation metric | `not-a-claim` |
| `Sec. 5` | Experiments: 19 benchmarks against FaMoS and IHYDE, measurement and process noise, real-world data (Tables 1-3, Figs. 9-10). | n/a — experiments | `not-a-claim` |

## Findings

**`Eq. 5` — the Gram matrix on the wrong side.** The paper stacks the data as columns,
`Φ = [φ(x(t_{j-w}), u(t_{j-w})), …, φ(x(t_{j+w}), u(t_{j+w}))] ∈ ℝ^{v×(2w+1)}`, and prints
`A = Ẋ(ΦᵀΦ)⁻¹Φᵀ`, the formula for data stacked as rows. `ΦᵀΦ` is `(2w + 1) × (2w + 1)` of rank
at most `v` and is singular as soon as `2w + 1 > v` (`det_transpose_mul_self_eq_zero`); the
paper's grid takes `w` from `⌈0.5(v - 1)⌉` up to ten times that, so the printed inverse does
not exist for almost every `w` it tries. The minimizer of (4) is `ẊΦᵀ(ΦΦᵀ)⁻¹` when `ΦΦᵀ` is
invertible (`pinv_leastSquares`), and (6), which the paper and CORA use, is right
(`dmdCandidate_leastSquares`).
[`GramTransposeSingular.lean`](../../src/CORALean/Global/GramTransposeSingular.lean)

**`Thm. 1` — what is proved.** The paper calls an automaton executable when the two errors it
names cannot occur: a state outside the target's invariant after a transition, and leaving an
invariant without hitting a guard. Its proof sketch argues three things, and these are what
`SplitTree.executable` proves for any tree of hyperplane splits and any affine reset per
surface: the leaves' polytopes cover `ℝⁿ`; a boundary point of a leaf's polytope lies on one of
its surfaces, and there in the `Prop. 1` guard towards whichever leaf contains its reset; and
each such guard maps into its target. Sec. 3.3 does not say which transitions are created; the
formalization creates one per surface of a leaf and target leaf. It also says nothing of the
flows: urgent transitions on a surface shared by two leaves can alternate without time
passing, and with a polynomial template `ẋ = Aᵢφ(x, u)` can escape to infinity in finite time
inside an unbounded invariant; the experiments use affine templates, whose flows exist for all
time. CORA's `priv_identify_decisionTree2automaton` bloats each invariant by `10⁻³` and adds
guards only on surfaces two leaves share with opposite normals.
[`SplitTreeExecutable.lean`](../../src/CORALean/HybridDynamics/Theorems/SplitTreeExecutable.lean)
