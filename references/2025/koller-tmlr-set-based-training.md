# Set-Based Training for Neural Network Verification

L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification". Transactions on Machine Learning Research (TMLR), 2025.

**Source:** https://arxiv.org/pdf/2401.14961 (arXiv:2401.14961v4, dated 5 Aug 2025 like the TMLR publication, https://openreview.net/forum?id=n0lzHrAWIA; 29 pages with the appendix, read in full; text extracted with `pypdf`, Prop. 5, 8 and 9 checked against the page images)  
**Inventory:** confirmed (against the paper: Definitions 1-7, Propositions 1-17 and Algorithms 1-2, each with its own counter, and Equations 1-12; the proofs are Appendix D, Sec. 5 and Appendices A-C are the evaluation)

What CORA's `neuralNetwork/train` does with `'set'`: propagate the zonotope of an `ℓ∞` ball through
the network, take the gradient of a set-based loss with respect to the output zonotope, a
*gradient set* with a gradient for every generator entry, and push it back through the layers.
`evaluateZonotopeBatch` is the image enclosure of Alg. 1 per neuron: the secant slope (Def. 7) and
the extremal approximation errors (Def. 6, Prop. 10), which Prop. 11 compares with DeepZ's. The
set-based loss, the F-radius and the layer enclosure are here, with their gradients and their
approximation errors; the F-radius gradient of Prop. 8 and the loss gradient of Prop. 9 are off by
a factor of the output dimension as printed (CORA divides correctly, see Findings). The set-based
backpropagation through a linear layer and the weight and bias gradients (Props. 13 and 14) are
proved by the chain rule, for a loss differentiable at the layer's output, and so is the
backpropagation through the image enclosure (Prop. 12 and the nonlinear case of Prop. 13), for a
slope and errors differentiable in the input's row. The running times, Props. 15-17, are asserted
per operation and bounded by the printed `O(·)`, with `n_max` covering the input width, which
Props. 16 and 17 leave out (see Findings).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | The cross-entropy error `L_CE(t, y) = -Σᵢ t(i) ln p(i)` with `p(i) = exp(y(i)) / (exp(y) 1)`. | n/a — restated from Bishop, Pattern Recognition and Machine Learning, Sec. 4.3.4, a book with no page here | `restated` |
| `Eq. 2` | The training goal: `min_θ Σ_{(x_i, t_i) ∈ D} L(t_i, Φ_θ(x_i))`. | n/a — the training problem, not a claim | `not-a-claim` |
| `Eq. 3` | The gradient of the loss with respect to the output of layer `k`, `g_k := ∇_{h_k} L(t, y)`. | n/a — notation | `not-a-claim` |
| `Eq. 4` | The update `W_k ← W_k - η ∇_{W_k} L = W_k - η g_k h_{k-1}ᵀ`, `b_k ← b_k - η g_k`. | n/a — restated from Bishop, Sec. 5.3, the weight gradient of a linear layer, a book with no page here; `Prop. 14` is its set-based version | `restated` |
| `Def. 1` | A feed-forward neural network: `h_0 = x`, `h_k = L_k(h_{k-1})` with `L_k` affine, `W_k h_{k-1} + b_k`, or an elementwise activation `ϕ_k(h_{k-1})`, `y = h_κ`. | n/a — restated from Bishop, Sec. 5.1, a book with no page here | `restated` |
| `Prop. 1` | (Backpropagation, Bishop Sec. 5.3) `g_κ = ∇_y L(t, y)`, `g_{k-1} = W_kᵀ g_k` at a linear layer and `Diag(ϕ_k'(h_{k-1})) g_k` at an activation, `k = κ, …, 1`. | n/a — restated from Bishop, a book with no page here | `restated` |
| `Def. 2` | A zonotope `Z = {c + Σᵢ G(i,·) β(i) \| β ∈ [-1, 1]} = ⟨c, G⟩_Z`. | n/a — restated; tracked as `Def. 1` on [Reachability of Uncertain Linear Systems Using Zonotopes](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Prop. 2` | (Interval enclosure, Althoff 2010, Prop. 2.2) `Z ⊆ [l, u]`, `l = c - \|G\| 1`, `u = c + \|G\| 1`, computed in `O(nq)`. | n/a — restated; tracked as `Prop. 2.7` on [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](../2023/ladner-hscc-abstraction-refinement.md), the same enclosure of a zonotope from the same source | `restated` |
| `Prop. 3` | (Minkowski sum, Althoff 2010, Prop. 2.1 and Sec. 2.4) `Z ⊕ I = ⟨c + ½(u + l), [G ½Diag(u - l)]⟩_Z` for an interval `I = [l, u]`, in `O(n)`. | n/a — restated from [Reachability Analysis and its Application to the Safety Assessment of Autonomous Cars](../2010/althoff-thesis.md), whose page does not list this chapter; the sum is `Sec. 2` on [Reachability of Uncertain Linear Systems Using Zonotopes](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Prop. 4` | (Affine map, Althoff 2010, Sec. 2.4) `f(Z) = W Z ⊕ b = ⟨Wc + b, WG⟩_Z`, in `O(mnq)`. | n/a — restated; tracked as `Sec. 2` on [Reachability of Uncertain Linear Systems Using Zonotopes](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Prop. 5` | (F-radius, Combastel 2015, Def. 3) For `Z = ⟨c, G⟩_Z ⊂ ℝⁿ`, `‖Z‖_F := (1/n) √(Σᵢ Σⱼ G(i,j)²)`, with a normalization factor `1/n` over Combastel's. | [`FRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/FRadius.lean), [`FRadiusEqFrobenius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FRadiusEqFrobenius.lean) — the Frobenius norm of the generator matrix over `n` | `correct` |
| `Def. 3` | The gradient of `f(·)` with respect to a zonotope: `∇_Z f(Z) := ⟨∇_c f(Z), ∇_G f(Z)⟩_Z`, the centre the derivative with respect to the centre and the generator matrix that with respect to the generator matrix. | [`Gradient.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/Gradient.lean), [`FderivEqGradient.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FderivEqGradient.lean) — the partial derivatives along each entry, `deriv`, zero where `f` is not differentiable along one; and where `f` is differentiable its derivative in a direction is read off the gradient set | `correct` |
| `Eq. 5` | A neural network classifies `x` correctly if `arg max_k y(k) = l`, the target label. | n/a — restated from [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](../2023/ladner-hscc-abstraction-refinement.md)'s setting (Ladner and Althoff 2023, Prop. B.2), which has no row for it | `restated` |
| `Eq. 6` | The input set `π_ε(x) := ⟨x, εI_{n_0}⟩_Z = {x̃ \| ‖x̃ - x‖_∞ ≤ ε}`. | n/a — the setting: an `ℓ∞` ball as a zonotope | `not-a-claim` |
| `Eq. 7` | The unsafe set `U_l = {y \| ∃k: y(k) > y(l)} = {y \| (I_{n_κ} - e_lᵀ 1) y > 0}`, `e_l` the `l`-th basis vector. | n/a — restated from Ladner and Althoff 2023, Prop. B.2; the matrix `I - e_lᵀ1` has the dimensions of a scalar subtracted from a matrix, the intended `I - 1 e_lᵀ` having the rows `y(k) - y(l)` | `restated` |
| `Eq. 8` | `Y ∩ U = ∅ ⟹ Y* ∩ U = ∅` for an enclosure `Y ⊇ Y* = Φ_θ(X)`. | n/a — restated; tracked as `Prop. 2.14` on [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](../2023/ladner-hscc-abstraction-refinement.md), the enclosure being sound | `restated` |
| `Prop. 6` | (Set-based forward propagation, Ladner and Althoff 2023, Sec. 2.4) `H_0 = X`, `H_k = W_k H_{k-1} + b_k` at a linear layer and `enclose(ϕ_k, H_{k-1})` at an activation, `Y = H_κ ⊇ Φ_θ(X)`. | n/a — restated; tracked as `Prop. 2.14` on [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](../2023/ladner-hscc-abstraction-refinement.md) | `restated` |
| `Prop. 7` | (Neural network verification, Ladner and Althoff 2023, Sec. 2.4) `max_{y ∈ Y} (I_{n_κ} - e_lᵀ 1) y ≤ 0 ⟹ Y* ∩ U = ∅`. | n/a — restated from Ladner and Althoff 2023, Sec. 2.4 and Prop. B.2, which have no row; the printed matrix is as at `Eq. 7` | `restated` |
| `Def. 4` | Set-based training: given a set-based loss `L : ℝ^{n_κ} × 2^{ℝ^{n_κ}} → ℝ`, train with the gradient set `∇_Y L(t, Y)`, a different gradient for each `y ∈ Y`. | n/a — the training paradigm, not a claim | `not-a-claim` |
| `Sec. 2.5` | The problem: `min_θ Σ L(t_i, enclose(Φ_θ, π_ε(x_i)))`, to reduce the output sets and verify in polynomial time. | n/a — the training problem, not a claim | `not-a-claim` |
| `Def. 5` | The set-based loss `L(t, Y) := (1 - τ) L(t, c_κ) + (τ / ε) ‖Y‖_F` for `Y = ⟨c_κ, G_κ⟩_Z`, `L` a loss, `ε > 0` the perturbation radius, `τ ∈ [0, 1]`. | [`SetBasedLoss.lean`](../../src/CORALean/NN/Definitions/SetBasedLoss.lean) | `correct` |
| `Eq. 9` | The TRADES loss `L_TRADES(t, y) = L(t, y) + max_{x̃ ∈ π_ε(x)} (1/λ) L(y, Φ_θ(x̃))`, which `Def. 5` generalizes. | n/a — restated from H. Zhang, Y. Yu, J. Jiao, E. Xing, L. El Ghaoui and M. Jordan, "Theoretically Principled Trade-off between Robustness and Accuracy" (ICML 2019, Eq. 5), which has no page here | `restated` |
| `Sec. 3.1 (normalization)` | The F-radius of `Def. 5` is normalized by `ε` to ease tuning `τ`: "the ratio of the F-radii of output enclosure `Y` and input set `X = π_ε(x)`, `‖Y‖_F / ‖π_ε(x)‖_F = (1/ε) ‖Y‖_F`". | n/a — the motivation of a hyperparameter scaling, not a claim used later; `‖π_ε(x)‖_F` is `ε / √n_0` with `Prop. 5`'s normalization (`ε √n_0` without it), so the ratio is `(√n_0 / ε) ‖Y‖_F` and equals `(1/ε) ‖Y‖_F` at `n_0 = 1` | `not-a-claim` |
| `Prop. 8` | (Gradient of the F-radius) For `Y = ⟨c_κ, G_κ⟩_Z ⊂ ℝ^{n_κ}`, `∇_Y ‖Y‖_F = ⟨0, (1 / (n_κ ‖Y‖_F)) G_κ⟩_Z` (Eq. 13 in the proof). | [`FRadiusGradient.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FRadiusGradient.lean), [`FRadiusHasDerivAt.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FRadiusHasDerivAt.lean), [`FRadiusGradient.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/FRadiusGradient.lean) — corrected: the generator matrix is `G_κ / (n_κ² ‖Y‖_F)`, for `‖Y‖_F > 0`; and the counterexample to the printed form **Counterexample:** `Zonotope.fRadius_gradient_counterexample` | `fixed` — the gradient of `(1/n) √(Σ G²)` is `G / (n √(Σ G²)) = G / (n² ‖Y‖_F)`; the printed `G / (n ‖Y‖_F)` is that of the unnormalized norm `√(Σ G²)`, and in two dimensions with one generator `(1, 0)` (`‖Y‖_F = 1/2`) the entry is `1/2`, not `1`; see Findings |
| `Prop. 9` | (Set-based loss gradient) `∇_Y L(t, Y) = ⟨(1 - τ) ∇_{c_κ} L(t, c_κ), (τ / ε)(1 / (n_κ ‖Y‖_F)) G_κ⟩_Z`. | [`SetBasedLossGradient.lean`](../../src/CORALean/NN/Theorems/SetBasedLossGradient.lean), [`SetBasedLossGradient.lean`](../../src/CORALean/NN/Counterexamples/SetBasedLossGradient.lean) — corrected: the generator matrix is `(τ / ε) G_κ / (n_κ² ‖Y‖_F)`, the centre as printed, for a loss differentiable along each centre entry; and the counterexample to the printed form **Counterexample:** `setBasedLoss_gradient_counterexample` | `fixed` — `Prop. 8`'s factor again; at `n_κ = 2`, `τ = ε = 1`, zero loss and one generator `(1, 0)` the printed entry is `1`, the derivative `1/2`; see Findings |
| `Def. 6` | The approximation errors of a linear approximation `p` of `ϕ` within `[l, u]`: `e := min_{x ∈ [l,u]} ϕ(x) - p(x)`, `ē := max_{x ∈ [l,u]} ϕ(x) - p(x)`, so that `ϕ([l, u]) ⊆ p(x) ⊕ [e, ē]`. | [`ApproxError.lean`](../../src/CORALean/NN/Layers/Definitions/ApproxError.lean), [`ApproxErrorEnclosure.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ApproxErrorEnclosure.lean) — the infimum and supremum; the enclosure for `ϕ - p` continuous | `correct` |
| `Def. 7` | Within `[l, u]`, `ϕ` is approximated by `p(x) := m x` with `m := (ϕ(u) - ϕ(l)) / (u - l)`; the offset `d` does not affect the image enclosure, so w.l.o.g. `d = 0`. | [`SecantSlope.lean`](../../src/CORALean/NN/Layers/Definitions/SecantSlope.lean) | `correct` |
| `Prop. 10` | (Approximation errors for ReLU, tanh, σ) `e = min_{x ∈ P_ϕ ∩ [l,u]} ϕ(x) - p(x)` and `ē = max_{x ∈ P_ϕ ∩ [l,u]} ϕ(x) - p(x)` for `ϕ ∈ {ReLU, tanh, σ}`, `P_ReLU = {0, l, u}`, `P_tanh = {±tanh⁻¹(√(1 - m)), l, u}`, `P_σ = {±2 tanh⁻¹(√(1 - 4m)), l, u}`. | [`ApproxErrorIsExtreme.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ApproxErrorIsExtreme.lean), [`ExistsCriticalExtreme.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ExistsCriticalExtreme.lean), [`EqPmArtanhOfTanh.lean`](../../src/CORALean/NN/Layers/Theorems/Real/EqPmArtanhOfTanh.lean), [`ApproxErrorRelu.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ApproxErrorRelu.lean), [`ApproxErrorTanh.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ApproxErrorTanh.lean), [`ApproxErrorSigmoid.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ApproxErrorSigmoid.lean) — for every slope `m` and `l ≤ u`, the secant of `Def. 7` being the case of the paper; the two other points of each `P` are in `P` as `±`, `Real.artanh` | `correct` |
| `Eq. 10` | The area of an approximation in the input-output plane, `area([e, ē], [l, u]) := (u - l)(ē - e)`. | [`ApproxArea.lean`](../../src/CORALean/NN/Layers/Operations/ApproxArea.lean) | `correct` |
| `Prop. 11` | For an s-shaped `ϕ` and an interval `[l, u]`, with `[e, ē]` the errors of `Def. 6` and `7` and `e_S` the error of Singh's enclosure (Singh et al. 2018, Thm. 3.2), `area([e, ē], [l, u]) ≤ area([-e_S, e_S], [l, u])`. | [`ApproxAreaLe.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ApproxAreaLe.lean) — every pair of values of `ϕ - m x` differs by at most `2 e_S`, `e_S = deepZSShape`'s error. **As printed:** the paper leaves "s-shaped" undefined and its proof uses `ϕ' ≥ min(ϕ'(l), ϕ'(u))` on `[l, u]`, which a derivative rising up to some point and falling after it gives, and which the sigmoid and the hyperbolic tangent have; the points `x_ ≤ x̄` of its figure are not needed | `correct` |
| `Prop. 12` | (Backpropagation through image enclosure) For a nonlinear layer with input set `H_{k-1} = ⟨c_{k-1}, G_{k-1}⟩_Z`, `G_{k-1} ∈ ℝ^{n_{k-1} × p}`, and gradient set `G_k = ⟨c_k', G_k'⟩_Z`, `G_{k-1}(i) = m_k(i) G_k(i) + (c_k'(i) c_{k-1}(i) + G_k'(i, [p]) G_{k-1}ᵀ(i, ·)) ∇_{H_{k-1}(i)} m_k(i) + ½(c_k'(i) + G_k'(i, p+i)) ∇_{H_{k-1}(i)} e_k(i) + ½(c_k'(i) - G_k'(i, p+i)) ∇_{H_{k-1}(i)} ē_k(i)`. | [`GradientImageEnclosure.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GradientImageEnclosure.lean), [`BackpropEnclose.lean`](../../src/CORALean/ContSet/Zonotope/Real/Definitions/BackpropEnclose.lean), [`ImageEnclosure.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ImageEnclosure.lean), [`Row.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Row.lean) — the gradient set of `L(Diag(m) H ⊕ [e, ē])` with respect to `H` is `backpropEnclose`, entry by entry, for slope and errors any functions of the row `H(i)` differentiable there and a loss differentiable at the layer's output | `underspecified` — the chain rule of the proof needs the loss differentiable at the output (as at `Prop. 13 (linear)`) and `m(i)`, `e(i)`, `ē(i)` differentiable in `H(i)`, which the statement leaves open and the secant slope of `Def. 7` is not where a generator entry is `0`; the printed `m_k(i) 𝒢_k(i)` has the output's `p + n_k` generators, its first `p` meant; see Findings |
| `Prop. 13 (linear)` | (Set-based backpropagation) At a linear layer, `G_{k-1} = W_kᵀ G_k`, `G_k = ⟨c_k', G_k'⟩_Z` (the proof applies the chain rule, Eq. 19 and 26). | [`GradientAffine.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GradientAffine.lean) — `∇_{H_{k-1}}` of `L(W H + b)` is `⟨Wᵀ c', Wᵀ G'⟩`, the transpose applied to the centre and every generator, for a loss differentiable at the layer's output | `underspecified` — the proof's chain rule needs the loss differentiable at the layer's output in the centre and generator entries together, which the statement leaves open; see Findings |
| `Prop. 13 (nonlinear)` | (Set-based backpropagation) `G_κ = ∇_Y L(t, Y)` and, at a nonlinear layer, `G_{k-1} = backpropEnclose(ϕ_k, G_k)` of `Prop. 12`, for `k = κ, …, 1`. | [`GradientImageEnclosure.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GradientImageEnclosure.lean) — at a nonlinear layer `∇_{H_{k-1}} L = backpropEnclose(ϕ_k, ∇_{H_k} L)`, which is `Prop. 12` | `underspecified` — as at `Prop. 12`: the loss differentiable at the layer's output, the slope and errors in the row; see Findings |
| `Eq. 11` | The gradient set of layer `k`, `G_k = ⟨c_k', G_k'⟩_Z := ∇_{H_k} L(t, Y)`. | n/a — notation | `not-a-claim` |
| `Prop. 14` | (Gradient set of weights and biases) `∇_{W_k} L(t, Y) = ∇_{H_k} L(t, Y) ⊙ H_{k-1}ᵀ` and `∇_{b_k} L(t, Y) = ∇_{H_k} L(t, Y) ⊙ ⟨1, 0⟩_Zᵀ`, with `Z_1 ⊙ Z_2ᵀ := c_1 c_2ᵀ + G_1 G_2ᵀ`. | [`GradientWeights.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GradientWeights.lean), [`GradientBias.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GradientBias.lean) — the derivative of `L(W H + b)` along the entry `W(i,j)` is `c'(i) c(j) + Σₗ G'(l,i) G(l,j)`, and along `b(i)` it is `c'(i)`, `c' · 1 + G' · 0`, for a loss differentiable at the layer's output | `underspecified` — as at `Prop. 13 (linear)`: the chain rule needs the loss differentiable at the layer's output, which the statement leaves open; see Findings |
| `Eq. 12` | The updates `W_k ← W_k - η ∇_{W_k} L(t, Y)`, `b_k ← b_k - η ∇_{b_k} L(t, Y)`. | n/a — the update rule of a training step, not a claim | `not-a-claim` |
| `Alg. 1` | The image enclosure of a nonlinear layer: bounds `[l, u]` of `H_{k-1}` (Prop. 2); per neuron the slope `m_k(i)` (Def. 7) and the errors `e_k(i)`, `ē_k(i)` (Prop. 10); `H̃_k ← Diag(m_k) H_{k-1} + ½(e_k + ē_k)` (Prop. 4); `H_k ← H̃_k ⊕ [e_k, ē_k]` (Prop. 3). | [`ApproxErrorRelaxation.lean`](../../src/CORALean/NN/Layers/Definitions/ApproxErrorRelaxation.lean), [`ApproxErrorRelaxationSound.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ApproxErrorRelaxationSound.lean), [`EncloseNonlinearPrinted.lean`](../../src/CORALean/NN/Layers/Definitions/EncloseNonlinearPrinted.lean), [`EncloseNonlinearPrinted.lean`](../../src/CORALean/NN/Layers/Counterexamples/Real/EncloseNonlinearPrinted.lean) — as a `Relaxation` for `Layer.activation`, sound for every continuous `ϕ`; and the printed lines in one dimension with the counterexample the printed form is refuted by `encloseNonlinearPrinted_counterexample` | `underspecified` — an `Alg.` row, read as simplified pseudocode (references/README.md), though the slip is not harmless: line 6 adds `½(e + ē)` to the centre and line 7 forms `⊕ [e, ē]`, which by `Prop. 3` adds the midpoint again; at `ϕ(x) = x + 1` on `[-1, 1]` the printed output is `[1, 3]` and misses `ϕ(-1) = 0`; the relaxation adds it once, which is what `Prop. 12`'s proof uses (`c_k(i) = m_k(i) c_{k-1}(i) + ½(e_k(i) + ē_k(i))`); see Findings |
| `Prop. 15` | (Time complexity of Alg. 1) For `H_{k-1} = Z` with `c ∈ ℝⁿ`, `G ∈ ℝ^{n × q}`, Alg. 1 takes `O(n² q)`. | [`ImageEnclosureCost.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Time/Operations/ImageEnclosureCost.lean), [`ImageEnclosureCostLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Time/Theorems/ImageEnclosureCostLe.lean),  — the cost asserted as the proof counts `Alg. 1`, the slope and errors at a constant per neuron, and proved at most `(cNeuron + 10) n² q` for `n, q ≥ 1` | `correct` |
| `Prop. 16` | (Time complexity of Prop. 6) The zonotopes of a forward propagation have at most `q ≤ n_0 + Σ_{k ∈ [κ]} n_k` generators, and the propagation takes `O(n_max² q κ)`, `n_max := max_k n_k`. | [`ForwardHLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Space/Theorems/ForwardHLe.lean), [`ForwardCost.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Time/Operations/ForwardCost.lean), [`ForwardCostLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Time/Theorems/ForwardCostLe.lean) — the generators: the forward propagation of a `SetBasedNet` adds at most `Σₖ nₖ`; the running time asserted as the proof counts it and proved at most `(cNeuron + 10) N² Q κ` for `N` at least every width, the input's included, and `Q` the generator bound | `underspecified` — `n_max = max_{k ∈ [κ]} nₖ` leaves out `n₀`, which the proof's `O(n_{k-1} nₖ q) = O(n_max² q)` needs at `k = 1`: a wide input before a narrow layer costs `n₀ n₁ q`, more than any constant times `n_max² q κ` once `n₀ ≫ n_max`; the formalization takes `n_max` over every width; see Findings |
| `Alg. 2` | One iteration of set-based training: `H_0 ← ⟨x, εI_{n_0}⟩_Z`, the set-based forward propagation, `G_κ ← ∇_Y L(t, Y)`, then for `k = κ, …, 1` the set-based backpropagation and, at a linear layer, the updates of `W_k` and `b_k`. | n/a — a training iteration, a procedure; what it computes is `Props. 8`-`14` and `Alg. 1`, each its own row | `not-a-claim` |
| `Prop. 17` | (Time complexity of Alg. 2) Alg. 2 takes `O(n_max² q κ)`. | [`TrainingCost.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Time/Operations/TrainingCost.lean), [`TrainingCostLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Time/Theorems/TrainingCostLe.lean) — the cost asserted as the proof counts `Alg. 2`, with constants per neuron for the enclosure, the loss gradient and the gradients of slope and errors, and proved at most `2 C N² Q κ` for `κ ≥ 1`, `N` and `Q` as at `Prop. 16` | `underspecified` — as at `Prop. 16`, `n_max` has to cover `n₀`; see Findings |
| `Sec. 5` | The evaluation: set-based training against TRADES, IBP and SABR on MNIST, CIFAR-10, SVHN and TinyImageNet (clean, falsified and fast-verified accuracy, Tables 1-2, Figs. 7), ablations on the loss weight `τ`, the input set and the volume heuristic, and the training details of Appendices A-C. | n/a — experiments | `not-a-claim` |

## Findings

**`Prop. 8` and `Prop. 9` — a factor of `n_κ`.** `Prop. 5` defines the F-radius with a
normalization factor `1/n`, `‖Y‖_F = (1/n) √(Σ G²)`, and `Prop. 8` prints the gradient as
`G / (n ‖Y‖_F)`. The proof writes the derivative of `(1/n) √(1ᵀ(G ⊙ G)1)` as `G / (n ‖Y‖_F)`
(Eq. 13), which drops the factor `1/n` hidden in `‖Y‖_F`: `∂/∂G(i,j) (1/n) √S = (1/n) G(i,j) / √S`
and `√S = n ‖Y‖_F`, so the gradient is `G / (n² ‖Y‖_F)`. The printed formula is the gradient of
the unnormalized Frobenius norm `√S` divided by `n`, which is the same thing written with `‖Y‖_F`
read as `√S`. In two dimensions the zonotope with one generator `(1, 0)` has `‖Y‖_F = 1/2` and
derivative `1/2` along the entry, where the printed formula gives `1`
([`FRadiusGradient.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/FRadiusGradient.lean)).
`Prop. 9` takes the factor over: its generator matrix is `(τ/ε) G / (n_κ ‖Y‖_F)`, again a factor
`n_κ` too large against the loss `Def. 5` ([`SetBasedLossGradient.lean`](../../src/CORALean/NN/Counterexamples/SetBasedLossGradient.lean)).
The corrected statements are proved ([`FRadiusGradient.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FRadiusGradient.lean),
[`SetBasedLossGradient.lean`](../../src/CORALean/NN/Theorems/SetBasedLossGradient.lean)). CORA's
`train.m` is right: it takes the plain Frobenius norm `√S` of the generator matrix, scales the
loss and the gradient `G / √S` by `1/(n_κ ε)` outside, which is `G / (n_κ² ε ‖Y‖_F)` per unit of
`τ`.

**`Prop. 13` and `Prop. 14` — differentiability.** Both are chain-rule statements: the loss reaches
`W_k` and `H_{k-1}` through the layer's output zonotope, and the proofs expand
`Σᵢ c_k'(i) ∂c_k(i) + Σᵢ Σⱼ G_k'(i,j) ∂G_k(i,j)`. That sum is the derivative of the loss
only if the loss is differentiable at the output in the centre and generator entries together; the
gradient set of `Def. 3` exists with partial derivatives alone, and then the formulas can fail. The
statements do not say, and the formalization assumes the total differentiability
(`DifferentiableAt` of the loss as a function of the centre and the generator entries).

**`Sec. 3.1` — the normalization of the F-radius.** The text derives the factor `1/ε` of `Def. 5`
as the ratio `‖Y‖_F / ‖π_ε(x)‖_F`, reading `‖π_ε(x)‖_F = ε`. With `Prop. 5`'s normalization
`‖π_ε(x)‖_F = (1/n_0) √(n_0 ε²) = ε / √n_0`, so the ratio is `√n_0 ‖Y‖_F / ε`; without it, `ε √n_0`.
The factor `1/ε` in the loss is a hyperparameter scaling and nothing later depends on the ratio.

**`Alg. 1` — the midpoint is added twice.** Line 6 forms `Diag(m_k) H_{k-1} + ½(e_k + ē_k)`, a
zonotope with centre `m c + ½(e + ē)`, and line 7 takes its Minkowski sum with the interval
`[e, ē]`, which by `Prop. 3` has centre `½(e + ē)`, so the centre becomes `m c + (e + ē)`: the
offset of the errors is added twice. For `ϕ(x) = x + 1` on any box the secant is `m = 1` and
`e = ē = 1`, and the printed output is the input shifted by `2`, not `1`. For the sigmoid on
`[0, 2]` and `H = ⟨1, [1]⟩`, `m ≈ 0.190`, `e = 0.5`, `ē ≈ 0.541`, the printed output is the
interval `[1.02, 1.44]`, which does not contain `σ(H) = [0.5, 0.88]`. The enclosure is
`Diag(m) H ⊕ [e, ē]` with the midpoint added once, which is `Prop. 12`'s own centre
`c_k(i) = m_k(i) c_{k-1}(i) + ½(e_k(i) + ē_k(i))` with the generators `½(ē - e)`; that is
`Layer.activation` of [`ApproxErrorRelaxation.lean`](../../src/CORALean/NN/Layers/Definitions/ApproxErrorRelaxation.lean),
sound by [`ApproxErrorRelaxationSound.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ApproxErrorRelaxationSound.lean).
Misprinted pseudocode, but false on an ordinary input, so `fixed`: [`EncloseNonlinearPrinted.lean`](../../src/CORALean/NN/Layers/Counterexamples/Real/EncloseNonlinearPrinted.lean)
proves the miss at `ϕ(x) = x + 1` on `[-1, 1]`.

**`Prop. 12` — differentiability, and the first term.** The proof differentiates the centre
`m(i) c(i) + ½(e(i) + ē(i))` and the generators `m(i) G(i, j)`, `½(ē(i) - e(i))` of the image
enclosure with respect to the row `H(i)`, by the chain and product rules, and so needs the slope
and the errors differentiable there; they are functions of the bounds `c(i) ∓ Σⱼ |G(i, j)|`
(`Def. 7`, `Prop. 10`), which have a kink where a generator entry is `0`, and the errors are
extremal values. As at `Prop. 13 (linear)` the loss must be differentiable at the output in the
centre and generator entries together. The statement assumes neither; the formalization takes
both, for any slope and errors that are functions of the row. The first term is printed
`m_k(i) 𝒢_k(i)`, a gradient set with the output's `p + n_k` generators, where the input's gradient
set has `p`: the proof's Eq. 25 sums over `j ∈ [p]`, the first `p` generators.
[`GradientImageEnclosure.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/GradientImageEnclosure.lean)

**`Prop. 16` and `Prop. 17` — the input width.** `n_max := max_{k ∈ [κ]} n_k` ranges over the
layers' outputs, and the proofs bound the `k`-th step's `O(n_{k-1} n_k q)` by `O(n_max² q)`, which at
`k = 1` needs `n₀ ≤ n_max`. A classifier's input is usually its widest layer (MNIST's `784` before
hidden layers of a few hundred), and a network of one linear layer from `n₀ = N` to `n₁ = 1`, with
the `q = N` generators of `⟨x, εI_N⟩`, costs `2N(N + 1) + 1` against `n_max² q κ = N`, so no
constant independent of `n₀` bounds it. With `n₀` held fixed the printed bound holds with a
constant depending on it; the formalization takes `n_max` over every width, the input's included.
[`ForwardCost.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Time/Operations/ForwardCost.lean), [`SetBasedNet.mul_mul_le_of_le`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Time/Theorems/Basic.lean), [`ForwardCostLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Complexity/Time/Theorems/ForwardCostLe.lean)
