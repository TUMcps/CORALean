# Reachset-Conformant System Identification

L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE Transactions on Automatic Control, 71(5):3014-3029, 2026.

**Source:** https://arxiv.org/pdf/2407.11692 (arXiv:2407.11692v3, 6 Aug 2025, the authors' version, 16 pages, read in full; text extracted with `pypdf`). Volume, issue and pages from the DOI record (doi:10.1109/TAC.2025.3633534); the typeset TAC article was not reachable, so the numbering is the arXiv version's. CORA cites the arXiv version, without result numbers, in `@contDynamics/conform.m`, `private/priv_conform_white.m`, `priv_conform_whiteCon.m`, `priv_conform_gray.m` and the `computeGO` methods of `linearSysDT`, `linearARX`, `nonlinearSysDT` and `nonlinearARX`.  
**Inventory:** confirmed (against arXiv v3: Definitions 1-7, Problem 1 with Problems 1.1-1.3, Theorems 1-2, Corollaries 1-2, Lemmas 1-4, Proposition 1 and Algorithms 1-4, each with its own counter; equations (1)-(25); Tables I-II)

Reachset-conformant identification beyond linear state-space models with additive
uncertainty: any model is linearized along a reference into a *general linear output*
(GLO) approximation `τ̄`, whose reachable set `Ȳ` is exact and, with the linearization
error `Ê`, encloses the model's (`Thm. 1`); for stretched zonotope templates `Ȳ` is a
zonotope linear in the unknowns (`Lemma 1`), so that containment of the measurements is a
set of linear constraints in two forms (`Lemma 3`, `Lemma 4`) and the white-box
identification a linear program (`Alg. 1`, `Thm. 2`). The algebra of the GLO matrices for
state-space (`Cor. 1`) and input-output (`Cor. 2`) models is formalized.
Gray- and black-box identification are nonlinear-programming and genetic-programming
searches around that program and are not covered.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Generator representation of zonotopes [35]) `Z = {c + Σᵢ λᵢ gᵢ \| λᵢ ∈ [-1, 1]} = ⟨c, G⟩`. | n/a — restated from Kühn 1998 [35]; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Def. 2` | (Halfspace representation of zonotopes [36]) `Z = {x \| N x ≤ d}`, obtained by [36, Thm. 7]. | n/a — restated from Althoff, Stursberg and Buss 2010 [36]; tracked as `Thm. 7` on [Althoff, Stursberg, Buss 2010](../2010/althoff-nahs-zonotopes-polytopes.md) | `restated` |
| `Def. 3` | (Interval norm of zonotopes [31, Sec. 3.1]) `‖Z‖_I = 1ᵀ\|G\|1`. | n/a — restated from Althoff 2023 [31]; tracked as `Eq. 11` on [Althoff 2023](../2023/althoff-arch-reachset-conformance.md) | `restated` |
| `Def. 4` | (Test case) The nominal initial state `x∗,₀⁽ᵐ⁾` and nominal inputs `u∗⁽ᵐ⁾`, executed `n_s` times with measured outputs `y_k⁽ᵐ'ˢ⁾`. | [`Conformant.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/Conformant.lean) — `TestCase`, one per execution | `correct` |
| `Def. 5` | (Reachable set) `Y_k⁽ᵐ⁾ = {τ_k(x₀, u₀:ₖ) \| x₀ ∈ x∗,₀⁽ᵐ⁾ ⊕ X₀⁽ᵐ⁾, u₀:ₖ ∈ u∗,₀:ₖ⁽ᵐ⁾ ⊕ U₀:ₖ⁽ᵐ⁾}`. | [`Glo.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/Glo.lean) — `reachSetOf`, for any output map `τ` | `correct` |
| `Def. 6` | (Reachset conformance [1, Sec. 3.5]) `S_T conf_R S_M ⇔ ∀m, k: Y_k⁽ᵐ⁾(S_T) ⊆ Y_k⁽ᵐ⁾(S_M)` (1). | n/a — restated from Roehm et al. 2019 [1, Sec. 3.5] | `restated` |
| `Eq. 2` | The target system's reachable set as the limit of its measurements over `n_s → ∞` executions. | n/a — a modelling approximation by samples | `not-a-claim` |
| `Eq. 3` | The uncertainty sets `X₀ = ⟨c_x + c_Δ,x, G_x diag(α_x)⟩`, `Uᵢ = ⟨c_u + c_Δ,u, G_u diag(α_u)⟩`, `α ≥ 0`. | [`TemplateZono.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/TemplateZono.lean) | `correct` |
| `Problem 1` | (Reachset-conformant identification) `q* = argmin Σₘ Σₖ wₖ r(Ŷₖ⁽ᵐ⁾)` (4a) s.t. `∀m, k, s: yₖ⁽ᵐ'ˢ⁾ ∈ Ŷₖ⁽ᵐ⁾` (4b); white-, gray- and black-box variants 1.1-1.3. | n/a — a problem statement | `not-a-claim` |
| `Def. 7` | (GLO approximation) `τ̄ₖ(x₀, u₀:ₖ) = ȳₖ + C̄ₖ(x₀ - x̄₀) + Σᵢ D̄ₖ,ᵢ(uᵢ - ūᵢ)` (5), `ēₖ = τₖ - τ̄ₖ`. | [`Glo.lean`](../../src/CORALean/ContDynamics/Conform/Definitions/Glo.lean) — `glo` | `correct` |
| `Thm. 1` | (Reachability using the GLO approximation) `Ŷₖ = Ȳₖ ⊕ Êₖ` (6) encloses the reachable set, `Ȳₖ = ȳₖ ⊕ C̄ₖ(-c_x ⊕ X₀) ⊕ ⨁ᵢ D̄ₖ,ᵢ(-c_u ⊕ Uᵢ)` (7) along `x̄₀ = x∗,₀ + c_x`, `ūᵢ = u∗,ᵢ + c_u` (8); (7) is the GLO approximation's exact reachable set. | [`ReachSetOfGlo.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ReachSetOfGlo.lean), [`ReachSetOfSubset.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/ReachSetOfSubset.lean) — the equality for `τ̄`, and the enclosure for any `τ` whose errors `Ê` holds | `correct` |
| `Cor. 1` | (State-space models) The GLO approximation of `x_{k+1} = f(xₖ, uₖ)`, `yₖ = g(xₖ, uₖ)` has `ȳₖ = g(x̄ₖ, ūₖ)`, `C̄ₖ = Cₖ ∏_{l=1}^k A_{k-l}`, `D̄ₖ,ᵢ = Cₖ ∏_{l=1}^{k-i-1} A_{k-l} Bᵢ` (`i < k`), `D̄ₖ,ₖ = Dₖ` (11), and `Êₖ = Cₖ ⨁_{j<k} ∏ A_{k-l} L̂_x,ⱼ ⊕ L̂_y,ₖ`; `Ê = 0` for linear models. | [`GloStateSpace.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/GloStateSpace.lean) — the output equals `τ̄ₖ + ēₖ` with these matrices and the printed `ēₖ`, for any remainders `l_x`, `l_y` of the linearizations (12)-(13); their enclosure by `L̂` (Taylor terms, cited from [41]) is a hypothesis | `correct` |
| `Cor. 2` | (Input-output models) For the NARX model (14), `C̄ₖ = E ∏_{l=0}^{k-n_p} A_ext,k-l`, `D̄ₖ,ᵢ = E Σⱼ (∏_{l<j} A_ext,k-l) B_ext,k-j,k-i-j` (15), and `Êₖ` likewise; `Ê = 0` for ARX models. | [`GloInputOutput.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/GloInputOutput.lean), [`NarxWindowStep.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/NarxWindowStep.lean), [`NarxAext.lean`](../../src/CORALean/ContDynamics/Conform/Operations/NarxAext.lean), [`NarxBext.lean`](../../src/CORALean/ContDynamics/Conform/Operations/NarxBext.lean), [`NarxE.lean`](../../src/CORALean/ContDynamics/Conform/Operations/NarxE.lean) — for `k ≥ n_p`, the output equals `ȳₖ + C̄ₖ(x₀ - x̄₀) + Σᵢ D̄ₖ,ᵢ(uᵢ - ūᵢ) + ēₖ` with (15b), (15c) and the printed `ēₖ = E Σⱼ (∏_{l<j} A_ext,k-l) Eᵀ lₖ₋ⱼ`, for any remainders `lₖ` of the first-order expansion (the Taylor hypothesis on `h`; their enclosure by `L̂` is cited from [41]); a linear `h` has `l = 0` | `underspecified` — `B_ext,k-j,k-i-j` needs the Jacobian block `B_{k,i}` at lags outside `0 ≤ i ≤ n_p`, which `h` does not have; read as zero, see Findings |
| `Lemma 1` | (Set of output deviations) Under (3), `cen(Ȳₖ) = ȳₖ + C̄ₖ c_Δ,x + Σᵢ D̄ₖ,ᵢ c_Δ,u` (16a), `gen(Ȳₖ) = gen'(Ȳₖ) diag([α_x; α_u; …; α_u])` (16b), `gen' = [C̄ₖ G_x, D̄ₖ,₀ G_u, …, D̄ₖ,ₖ G_u]` (16c). | [`GloSetTemplateZono.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/GloSetTemplateZono.lean) — an equality of sets | `correct` |
| `Lemma 2` | (Cost function) With `r(Ŷ) = ‖Ȳ‖_I`, the cost (4a) is `γα`, `α ≥ 0`, `γ = Σₘ Σₖ wₖ 1ᵀ[\|C̄ G_x\|, Σᵢ \|D̄ᵢ G_u\|]` (17). | [`GloCostEq.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/GloCostEq.lean), [`IntervalNormSmul.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/IntervalNormSmul.lean) | `correct` |
| `Lemma 3` | (Halfspace constraints) `yₖ⁽ᵐ'ˢ⁾ ∈ Ȳₖ⁽ᵐ⁾ ∀s` is equivalent to `maxₛ(N y_a,ₖ⁽ᵐ'ˢ⁾) ≤ P_α α + P_c c_Δ` (18), `α ≥ 0`, `P_α = [\|N C̄ G_x\|, Σᵢ \|N D̄ᵢ G_u\|]`, `P_c = [N C̄, N Σᵢ D̄ᵢ]`, `N` from the halfspace representation of `Ȳ`. | [`MemGloSetIffHRep.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemGloSetIffHRep.lean), [`MemTemplateZonoIff.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemTemplateZonoIff.lean) — per execution; `N` any family carrying both signs of the template's cross-product normals, fixed before `α`, with the template spanning the output space | `correct` |
| `Lemma 4` | (Generator constraints) The same containment is equivalent to `∃β: 0 ≤ R_α α ± β` (19a) and `y_a = Q_c c_Δ + Q_β β` (19b), `α ≥ 0`. | [`MemGloSetIffGen.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/MemGloSetIffGen.lean) | `correct` |
| `Alg. 1` | (White) Compute the GLO approximations, `γ`, set `B_c = I` for nonlinear models, solve `min γα` s.t. (18) or (19), `α ≥ 0`, `B_c c_Δ = 0` (22), return `ℓ_C = γα*`. | [`WhiteConformant.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/WhiteConformant.lean), [`GloCostEq.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/GloCostEq.lean) — line 6's `argmin` is the solver's: every feasible point it may return is conformant, and line 7's cost is `γα` | `correct` |
| `Thm. 2` | (White-box identification of uncertainty sets) Problem 1.1 can be solved with Alg. 1. | [`WhiteConformant.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/WhiteConformant.lean), [`GloCostEq.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/GloCostEq.lean) — a feasible point of (22) satisfies (4b) whenever `0 ∈ Ê`, and its objective is (4a) at `r = ‖Ȳ‖_I` | `underspecified` — "solved" holds in the sense the proof gives: feasible points are conformant and the objective is the cost; the program's optimum is Problem 1.1's for linear models (`Ê = {0}`), for nonlinear ones only that of the stricter (23); see Findings |
| `Alg. 2` | (GraySim) A nonlinear program over the model parameters `p`, calling White at each iteration and once more at `p*`. | n/a — a nonlinear-programming search, a subject CORALean does not cover; its result's conformance is the final White call's (`Thm. 2`) | `not-covered` |
| `Alg. 3` | (GraySeq) A nonlinear program minimizing `ℓ_U` (24) over `p` and `c_Δ`, then White at `p*`. | n/a — a nonlinear-programming search, a subject CORALean does not cover; its result's conformance is the final White call's (`Thm. 2`) | `not-covered` |
| `Prop. 1` | (Underapproximative cost function) The minimum cost `γα*` of (22) is bounded below by `ℓ_U = Σₘ Σₖ wₖ 1ᵀ maxₛ \|y_a,ₖ⁽ᵐ'ˢ⁾ - y_Δ,ₖ⁽ᵐ⁾\|` (24), `y_Δ = [C̄, Σᵢ D̄ᵢ] B̃_c c_Δ`. | [`CostUnderApprox.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/CostUnderApprox.lean) — `ℓ_U ≤ γα` at every feasible point, `wₖ ≥ 0`, with `B̃_c c_Δ = c_Δ` as (22d) gives | `correct` |
| `Eq. 25` | The least-squares cost `ℓ_LS = Σₘ Σₖ wₖ 1ᵀ Σₛ (y_a,ₖ⁽ᵐ'ˢ⁾ - y_Δ,ₖ⁽ᵐ⁾)²`. | n/a — the definition of an alternative cost | `not-a-claim` |
| `Alg. 4` | (BlackCGP) Conformant genetic programming: least-squares then conformance-cost evolution of model functions, White on the best. | n/a — genetic programming, a subject CORALean does not cover | `not-covered` |
| `Sec. VII` | Scalability (Table I), white/gray/black-box comparison on four systems (Table II, Figs. 3-4), a vehicle model from real data. | n/a — experiments | `not-a-claim` |

## Findings

**`Thm. 2` — what "solved" means.** Problem 1.1 asks for the stretch factors and center
shifts minimizing `Σ wₖ r(Ŷₖ)` subject to every measurement lying in `Ŷₖ = Ȳₖ ⊕ Êₖ`. The proof
picks `r(Ŷ) = ‖Ȳ‖_I` and replaces `y ∈ Ŷ` by the stricter `y ∈ Ȳ` (23), valid once `0 ∈ Ê`.
What Alg. 1 then solves is (23): every point it returns is feasible for Problem 1.1, which is
the guarantee that matters for conformance and is what `white_conformant` proves, and its
objective is the printed cost (`gloCost_eq`). For a linear model `Ê = {0}` and (23) is
Problem 1.1 itself; for a nonlinear one a smaller `α` may already be conformant once `Ê`
is added, so Alg. 1's optimum need not be Problem 1.1's. The theorem holds in the first
sense, which the proof establishes.
[`WhiteConformant.lean`](../../src/CORALean/ContDynamics/Conform/Theorems/WhiteConformant.lean)

**`Cor. 2` — the input Jacobians outside the window.** (15c) sums `B_ext,k-j,k-i-j` over `j = 0, …, k-n_p`, so the lag `k-i-j` of the block `B_{k,·} = ∇_{u_{k-·}} h` leaves `0, …, n_p`: it is below `0` for `j` large and above `n_p` for `i` small. The expansion of `h` has no input beyond `u_{k-n_p}`, so the block there is `0`, which is what makes the formula the unrolling of the recursion. [`NarxBext.lean`](../../src/CORALean/ContDynamics/Conform/Operations/NarxBext.lean) is zero outside the range. With that reading every printed formula is exact.
