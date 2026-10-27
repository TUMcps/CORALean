# Out of the Shadows: Exploring a Latent Space for Neural Network Verification

```bibtex
@inproceedings{koller2026out,
  author = {Koller, L. and Ladner, T. and Althoff, M.},
  title = {Out of the Shadows: Exploring a Latent Space for Neural Network Verification},
  booktitle = {International Conference on Learning Representations},
  year = {2026}
}
```

**Source:** https://arxiv.org/pdf/2505.17854v3 (arXiv:2505.17854v3, 9 Feb 2026, "Published as a conference paper at ICLR 2026", 18 pages with the appendix, read in full, text extracted with `pymupdf`, Prop. 2, Prop. 3, Eq. 9 and Eq. 13 checked against the page images)  
**Inventory:** confirmed (against the paper: Definitions 1-3, Propositions 1-4, Corollary 1, Algorithm 1 and Example 1, each with its own counter, and Equations 1-15; the proofs are Appendices E-F, Sec. 5 and Appendices A and C are the evaluation)

CORA's `neuralNetwork/verify` with `options.nn.refinement_method = 'zonotack'` and
`options.nn.falsification_method = 'zonotack'`: a branch-and-bound over input sets that
propagates zonotopes (`SetBasedNet.forward`), drops a set whose output misses the unsafe set
`U = ⟨A, b⟩_H`, tries the vertex of the output nearest `U` as a counterexample, and otherwise
constrains the input set's own factors by the unsafe set (Prop. 2) and splits it. The latent
space is the generator factors: the input's `q₀` factors are the first `q₀` of the output's, so
`A y ≤ b` read on the output becomes `C β ≤ d` on the input. That needs the approximation errors
of each activation to bound `ϕ(t) - m t` pointwise, which Prop. 1's set-level enclosure does not
say (Findings). The constrained hypercube's bounds come from Prop. 3, a Fourier-Motzkin
elimination row by row, CORA's `conZonotope/approximateBoundsWithGPU`. The falsification vertex is
printed with the wrong sign, and the image of the factor bounds (Eq. 13) with signs that fit the
other reading of `A⁻` than the one Prop. 3 needs; both are corrected, CORA computes both right.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Neural network, Bishop 2006, Sec. 5.1) `h₀ = x`, `h_k = L_k(h_{k-1})` with `L_k` affine, `W_k h_{k-1} + b_k`, or an elementwise activation `ϕ_k(h_{k-1})`, `y = h_κ`. | n/a — restated from Bishop, Pattern Recognition and Machine Learning, Sec. 5.1, a book with no page here, as on [Set-Based Training for Neural Network Verification](../2025/koller-tmlr-set-based-training.md) | `restated` |
| `Def. 2` | (Zonotope, Girard 2005, Def. 1) `⟨c, G⟩_Z := {c + Σᵢ G(·,i) β(i) \| β ∈ [-1, 1]^q}`. | n/a — restated; tracked as `Def. 1` on [Reachability of Uncertain Linear Systems Using Zonotopes](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 1` | (Althoff 2010, Prop. 2.1 and Sec. 2.4) `Z ⊕ [x̲, x̄] = ⟨c + ½(x̲ + x̄), [G diag(½(x̄ - x̲))]⟩_Z`. | n/a — restated; the sum is tracked as `Sec. 2` on [Reachability of Uncertain Linear Systems Using Zonotopes](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 2` | (Althoff 2010, Sec. 2.4) `f(Z) = W Z ⊕ b = ⟨W c + b, W G⟩_Z` for `f(x) = W x + b`. | n/a — restated; tracked as `Sec. 2` on [Reachability of Uncertain Linear Systems Using Zonotopes](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Sec. 2.3 (polytope)` | A convex polytope `⟨A, b⟩_H = {x \| A x ≤ b}` (Althoff 2010, Def. 2.1), and by constraining the hypercube a zonotope represents every convex polytope (Scott et al. 2016, Thm. 1). | n/a — restated; tracked as `Thm. 1` on [Constrained zonotopes: A new tool for set-based estimation and fault detection](../2016/scott-automatica-constrained-zonotopes.md) | `restated` |
| `Def. 3` | (Constrained zonotope, Scott et al. 2016, Def. 3) For `Z = ⟨c, G⟩_Z` with `G ∈ ℝ^{n×q}`, `C ∈ ℝ^{p×q}` and `d ∈ ℝ^p`, `Z\|_{C≤d} := {c + G β \| β ∈ [-1, 1]^q, C β ≤ d} = c ⊕ G (B_q ∩ ⟨C, d⟩_H)`, with inequality constraints where Scott et al. have equalities. | [`Constrain.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/Constrain.lean), [`ConstrainConstructEqImage.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/ConstrainConstructEqImage.lean) — `Zonotope.constrain`, a `ConZonotope` whose factor constraints are the polytope `⟨C, d⟩_H`, and the second form as the image of the constrained box under `β ↦ c + G β` | `correct` |
| `Sec. 2.3 (constraints)` | Inequality and equality constraints are equivalent, translated by slack variables, and the Minkowski sum (1) and the affine map (2) are the same for zonotopes and constrained zonotopes (Scott et al. 2016, Prop. 1). | n/a — restated; tracked as `Prop. 1` on [Constrained zonotopes: A new tool for set-based estimation and fault detection](../2016/scott-automatica-constrained-zonotopes.md); the slack-variable remark justifies the representation, and `ConZonotope` holds inequality and equality constraints alike, as an `HPolytope` on the factors | `restated` |
| `Prop. 1` | (Set propagation, Ladner and Althoff 2023, Sec. 2.4) `H₀ = X`, `H_k = enclose(L_k, H_{k-1})`, `Y = H_κ ⊇ Φ(X)`, with `L_k(H_{k-1}) ⊆ enclose(L_k, H_{k-1})`; `W_k H_{k-1} ⊕ b_k` at a linear layer, `diag(m_k) H_{k-1} ⊕ [e̲_k, ē_k]` at an activation, `m_k(i)` the slope and `[e̲_k(i), ē_k(i)]` the approximation error of neuron `i` (Koller et al. 2025, Sec. IV). | n/a — restated; tracked as `Prop. 2.14` on [Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis](../2023/ladner-hscc-abstraction-refinement.md); the zonotope form is `Prop. 6` and `Alg. 1` of [Set-Based Training for Neural Network Verification](../2025/koller-tmlr-set-based-training.md), `SetBasedNet.forward` | `restated` |
| `Eq. 3` | The verification goal `Φ(X) ∩ U = ∅`. | n/a — the problem statement, not a claim | `not-a-claim` |
| `Eq. 4` | The falsification goal: `x ∈ X` with `Φ(x) ∈ U`. | n/a — the problem statement, not a claim | `not-a-claim` |
| `Sec. 3` | (Latent space) The propagation of a zonotope through the layers transforms the projection of the hypercube, not the hypercube; the input, hidden and output sets are "shadows" of the same hypercube, so each input `x` and its output `Φ(x)` are written with the same factors, the output with additional factors for the approximation errors (Eq. 6). | [`IsRelaxationOf.lean`](../../src/CORALean/NN/Definitions/IsRelaxationOf.lean), [`LeForwardH.lean`](../../src/CORALean/NN/Theorems/LeForwardH.lean), [`ForwardLatent.lean`](../../src/CORALean/NN/Theorems/ForwardLatent.lean) — `SetBasedNet.forward_latent`: for every factor `β ∈ B_{q₀}` of a point of `X` there is a factor `β' ∈ B_{q_κ}` of `Y = enclose(Φ, X)`, `β'` equal to `β` on the first `q₀` entries, with `Φ(c_x + G_x β) = c_y + G_y β'`, for a network whose activations' errors bound `ϕ(t) - m t` pointwise (`SetBasedNet.IsRelaxationOf`); CORA's `evaluateZonotopeBatch_`, which `verify.m` calls, appends the error generators after the input's | `underspecified` — the factors are shared only when each approximation error bounds `ϕ(t) - m t` at every point of the neuron's input range, which Prop. 1's `L_k(H) ⊆ enclose(L_k, H)` does not say; the formalization asks for it, and the hypercube grows by one factor per neuron rather than staying the same; see Findings |
| `Example 1` | The layer `x ↦ ReLU(2^{-1/2} [1 -1; 1 1] x + [1; 0])` on `X = ⟨0, 2^{-1/2} I₂⟩_Z` (Fig. 2); the unsafe set `y(1) ≥ 3/2` becomes `[-½ ½] β([2]) ≤ -½` on the input's factors, and the ReLU split `h₁ ≤ 0` becomes `[½ ½] β([2]) ≤ 0`. | n/a — an illustration of `Prop. 2`; the numbers are consistent: `H₁` and `Y` of Eq. 5 follow from Eq. 2 and Eq. 1 with the slopes `(1, ½)` and errors `[0, 0]`, `[0, ½]`, and `C`, `d` of Eq. 7 are `Prop. 2`'s, with Eq. 1's fourth generator, the zero error of the first neuron, left out of `Y` | `not-a-claim` |
| `Eq. 5` | `H₁ = ⟨[1; 0], ½ [1 -1; 1 1]⟩_Z` and `Y = ⟨[1; ¼], ¼ [2 -2 0; 1 1 1]⟩_Z`. | n/a — a step of `Example 1` | `not-a-claim` |
| `Eq. 6` | `x = 2^{-1/2} I₂ β([2])`, `y = [1; ¼] + [½ -½; ¼ ¼] β([2]) + [0; ¼] β(3)` for one `β ∈ [-1, 1]³`. | n/a — a step of `Example 1`, the instance of `Sec. 3` | `not-a-claim` |
| `Eq. 7` | `y(1) ≥ 3/2 ⟺ [-½ ½] β([2]) ≤ -½`, `C = [-½ ½]`, `d = -½`. | n/a — a step of `Example 1` | `not-a-claim` |
| `Prop. 2` | (Enclosing unsafe inputs) For `Φ`, `X = ⟨c_x, G_x⟩_Z` with `G_x ∈ ℝ^{n₀×q₀}`, `U = ⟨A, b⟩_H` and `Y = ⟨c_y, G_y⟩_Z = enclose(Φ, X)` an enclosure of the output set with `G_y ∈ ℝ^{n_κ×q_κ}`: `{x ∈ X \| Φ(x) ∈ U} ⊆ X\|_{C≤d} ⊆ X`, where `C := A G_y(·,[q₀])` and `d := b - A c_y + \|A G_y(·,[q_κ]∖[q₀])\| 1`. | [`UnsafeInputConstraints.lean`](../../src/CORALean/NN/Operations/UnsafeInputConstraints.lean), [`EncloseUnsafeInputs.lean`](../../src/CORALean/NN/Operations/EncloseUnsafeInputs.lean), [`EncloseUnsafeInputsOuter.lean`](../../src/CORALean/NN/Theorems/EncloseUnsafeInputsOuter.lean), [`EncloseUnsafeInputs.lean`](../../src/CORALean/NN/Counterexamples/EncloseUnsafeInputs.lean) — `SetBasedNet.encloseUnsafeInputs_outer`, both inclusions, for `Y = SetBasedNet.forward X` of a network with pointwise approximation errors; `SetBasedNet.encloseUnsafeInputs_counterexample`: with `ϕ(t) = -t`, slope `1` and errors `[0, 0]` on `X = [-1, 1]`, `Y ⊇ Φ(X)` and still the unsafe input `-1` of `U = {y ≥ ½}` is outside `X\|_{C≤d} = [½, 1]`. CORA: `aux_constructUnsafeInputSet` of `verify.m`, which keeps all `q_κ` factors as constraint columns and bounds the error factors by Prop. 3 together with the input's | `underspecified` — the proof's "the first `q₀` factors of the output `y` are the factors of the input `x`" is not implied by `Y` enclosing `Φ(X)`, nor by Prop. 1's set-level enclosure; it needs the approximation errors pointwise, which the formalization assumes; see Findings |
| `Sec. 3 (iteration)` | Prop. 2 can be iterated, each time transferring the unsafe set to the input space to remove provably safe inputs; the refined set encloses the unsafe inputs and in general not the full output set (Fig. 3). | n/a — a remark on using `Prop. 2`, not a claim beyond it | `not-a-claim` |
| `Eq. 8` | (Set-based verification, Scott et al. 2016, Prop. 2) `∃ i ∈ [p]: A(i,·) c_y - \|A(i,·) G_y\| 1 > b(i) ⟹ Y ∩ U = ∅`. | [`InterIneqsEqEmptyOfRow.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/InterIneqsEqEmptyOfRow.lean) — `Zonotope.inter_ineqs_eq_empty_of_row`; CORA: the `unknown` test of step 1 of `verify.m` | `correct` |
| `Eq. 9` | (Set-based falsification, Althoff and Frehse 2016, Lemma 1) For each normal vector `A(i,·)` of the unsafe set, the boundary point `β̃ᵢ = sign(A(i,·) G_y)`, `ỹ = c_y + G_y β̃ᵢ` of the intersection of the enclosed output set and the unsafe set, and the candidate `x̃ = c_x + G_x β̃ᵢ([q₀]) ∈ X`, checked by `Φ(x̃) ∈ U`. | [`ZonotackFactors.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ZonotackFactors.lean), [`ZonotackFactorsIsLeast.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ZonotackFactorsIsLeast.lean), [`SignBoundaryPoint.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/SignBoundaryPoint.lean) — corrected: `β̃ = -sign(A(i,·) G_y)` (`Zonotope.zonotackFactors`) gives the point of `Y` least in `A(i,·) y`, `Zonotope.zonotackFactors_isLeast`, so it satisfies row `i` whenever some point of `Y` does; CORA: the `'zonotack'` falsification of step 2.1 of `verify.m`, `beta_ = -sign(...)` **Counterexample:** `Zonotope.signBoundaryPoint_counterexample` | `fixed` — the printed sign maximizes `A(i,·) y` over `Y`, the vertex farthest from the halfspace `A(i,·) y ≤ b(i)`: for `Y = [-1, 1]` and `U = {y ≤ 0}`, `Y ∩ U = [-1, 0]` and the printed `ỹ = 1 ∉ U`; CORA takes `-sign`; see Findings |
| `Alg. 1` | (Set-based verification algorithm) A queue of input sets from `X`; per set `X_i`: `Y_i ← enclose(Φ, X_i)` (Prop. 1). If `Y_i ∩ U = ∅` (8) continue; else `x̃_i ← c_x + G_x β̃([q₀])` for `β̃_i = sign(A(i,·) G_y)` (9), `ỹ_i ← Φ(x)`, return `FALSIFIED(x̃_i)` if `ỹ_i ∈ U`. Else compute `C, d` (Prop. 2), split into `X_i\|_{C₁≤d₁}, …, X_i\|_{C_ξ≤d_ξ}` (Scott et al. 2016, Prop. 3) and enqueue them; `VERIFIED` when the queue is empty. | [`VerifyResult.lean`](../../src/CORALean/NN/Definitions/VerifyResult.lean), [`Verify.lean`](../../src/CORALean/NN/Operations/Verify.lean), [`IsVerifySound.lean`](../../src/CORALean/NN/Theorems/IsVerifySound.lean) — `SetBasedNet.verify`, the main loop of `verify.m` with `'zonotack'` falsification and refinement: a candidate per row of `A` with `-sign`, the pieces of a split stored as their factor bounds of Prop. 3 rescaling `X_i` (`aux_refineInputSet`, `aux_scaleAndOffsetZonotope`), an empty piece dropped, and a budget of sets that ends in `UNKNOWN` (`options.nn.max_verif_iter`). The split is a parameter, any family of constraints covering the factor box (`aux_dimSplitConstraints`, the neuron splits); `SetBasedNet.verify_sound`: `VERIFIED` proves every queued set safe, `FALSIFIED(x̃)` gives `x̃` in a queued set with `Φ(x̃) ∈ U` | `underspecified` — an `Alg.` row, read as simplified pseudocode (references/README.md): line 10 has the sign of `Eq. 9` and one `β̃_i` indexed by the loop counter `i`, line 11 reads `Φ(x)` for `Φ(x̃_i)`, line 15 applies Prop. 2, stated for a zonotope, to the constrained sets of line 16, which App. D stores as their bounds, and the loop has no budget; see Findings |
| `Sec. B (F-radius)` | The F-radius `‖Y‖_F := √(Σᵢ Σⱼ G_y(i,j)²)` of `Y = ⟨c_y, G_y⟩_Z` (Combastel 2015, Def. 3). | n/a — restated; tracked as `Def. 3` on [Zonotopes and Kalman observers: Gain optimality under distinct uncertainty paradigms and robust convergence](../2015/combastel-automatica-zonotopes-kalman.md) | `restated` |
| `Eq. 10` | (Enclosure-gradient heuristic) The score `s(i) = r(i) ∇_{r(i)} ‖Y‖_F` of input dimension `i`, `r = \|G_x\| 1` the radius of `X`. | n/a — a splitting heuristic, the choice of which dimension `Alg. 1` splits; `SetBasedNet.verify_sound` holds for every split that covers the factor box | `not-a-claim` |
| `Eq. 11` | The score `s(L_k, i) = e_k(i) ∇_{e_k(i)} ‖Y‖_F` of neuron `i` of a ReLU layer `k`, `e_k = ½(ē_k - e̲_k)` the radius of its approximation error. | n/a — a splitting heuristic, as `Eq. 10` | `not-a-claim` |
| `Eq. 12` | (Local-gradient heuristic, Ladner and Althoff 2023) `s(i) = r(i) ‖∇_{r(i)} y‖₂` and `s(L_k, i) = e_k(i) ‖∇_{e_k(i)} y‖₂` with `y = Φ(c_x)`. | n/a — the baseline heuristic of Tab. 4, as `Eq. 10` | `not-a-claim` |
| `Prop. 3` | (Bounds of bounded polytope) `P = ⟨C, d⟩_H ∩ [β̲₀, β̄₀] ⊂ ℝ^q` with `C ∈ ℝ^{p×q}` is enclosed by `[β̲, β̄]`: with `Σ_{∖{j}} := I_q - e_j e_jᵀ` and `C̲(i,j) := (d(i) - C⁺(i,·) Σ_{∖{j}} β̲₀ - C⁻(i,·) Σ_{∖{j}} β̄₀) / C(i,j)`, `β̲(j) = max ({C̲(i,j) \| C(i,j) < 0} ∪ {β̲₀(j)})` and `β̄(j) = min ({C̲(i,j) \| C(i,j) > 0} ∪ {β̄₀(j)})`; `A⁺ = ½(A + \|A\|) ∈ ℝ_{≥0}` and "`A⁻ ∈ ℝ_{≥0}` defined analogously". | [`FourierMotzkinBounds.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/FourierMotzkinBounds.lean), [`FourierMotzkinBoundsOuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/FourierMotzkinBoundsOuter.lean) — `ConZonotope.fourierMotzkinBounds_outer`, `P ⊆ [β̲, β̄]`, with `C⁻ = ½(C - \|C\|)`; CORA: `aux_fourierMotzkinApproximation` of `conZonotope/approximateBoundsWithGPU`, which `aux_refineInputSet` of `verify.m` calls | `underspecified` — the notation leaves `A⁻` open: "defined analogously" to `A⁺` with `A⁻ ∈ ℝ_{≥0}` reads `½(\|A\| - A)`, under which `C̲(i,j)` has the wrong sign on `C⁻`; the proof's last step, `min C(i,·) Σ_{∖{j}} β̃ = C⁺(i,·) Σ_{∖{j}} β̲₀ + C⁻(i,·) Σ_{∖{j}} β̄₀`, needs `C⁻ = ½(C - \|C\|) ≤ 0`, which the formalization takes; see Findings |
| `App. D` | Prop. 3 can be applied iteratively: for `P = ⟨C, d⟩_H ∩ [β̲₀, β̄₀]` with bounds `[β̲, β̄]`, `P = ⟨C, d⟩_H ∩ [β̲, β̄]`, and Prop. 3 applies again (App. A: at most 4 passes). | [`FourierMotzkinBoundsInterEq.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/FourierMotzkinBoundsInterEq.lean), [`FourierMotzkinIter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/FourierMotzkinIter.lean), [`FourierMotzkinIterOuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/FourierMotzkinIterOuter.lean) — `ConZonotope.fourierMotzkinBounds_inter_eq`, the equality, and `ConZonotope.fourierMotzkinIter_outer`, `k` passes from the unit box still enclose it; CORA: the `while tighterBnds && iter <= maxIter` loop of `aux_fourierMotzkinApproximation` | `correct` |
| `Eq. 13` | The bounds of `Z\|_{C≤d}` from bounds `[β̲, β̄] ⊆ B_q` of its constrained hypercube: `Z\|_{C≤d} ⊆ c ⊕ [G⁺ β̲ - G⁻ β̄, G⁺ β̄ - G⁻ β̲]`. | [`IntervalOfFactorBounds.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Operations/IntervalOfFactorBounds.lean), [`IntervalOfFactorBoundsOuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/IntervalOfFactorBoundsOuter.lean), [`IntervalOfFactorBoundsPrinted.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Counterexamples/IntervalOfFactorBoundsPrinted.lean) — corrected: `c ⊕ [G⁺ β̲ + G⁻ β̄, G⁺ β̄ + G⁻ β̲]` with `G⁻ = ½(G - \|G\|)`, the reading `Prop. 3` needs (`Zonotope.intervalOfFactorBounds_outer`); CORA: the `'fourier-motzkin'` branch of `aux_boundConZonotope`, `c + G β_c ± \|G\| β_r`, the same box **Counterexample:** `Zonotope.intervalOfFactorBoundsPrinted_counterexample` | `fixed` — with `G⁻ = ½(G - \|G\|)`, the reading under which `Prop. 3` holds, the printed `-G⁻` adds `\|G⁻\|` on the wrong side: for `Z = ⟨0, [-1]⟩_Z` and the exact bounds `[-1, 1]` the printed interval runs from `1` to `-1` and misses `0 ∈ Z`; under the other reading `Eq. 13` holds and `Prop. 3` fails; see Findings |
| `Prop. 4` | (Time complexity of Alg. 1) With `κ` layers, `p` output constraints, `q` generators of the output enclosure and `ξ` splits per iteration, an iteration of Alg. 1 takes `O(κ q³ + ξ p q²)` computation time with respect to `κ`, `p`, `q` and `ξ`. | [`EvalCost.lean`](../../src/CORALean/NN/Complexity/Time/Operations/EvalCost.lean), [`EvalCostLe.lean`](../../src/CORALean/NN/Complexity/Time/Theorems/EvalCostLe.lean), [`VerifyStepCost.lean`](../../src/CORALean/NN/Complexity/Time/Operations/VerifyStepCost.lean), [`VerifyStepCostLe.lean`](../../src/CORALean/NN/Complexity/Time/Theorems/VerifyStepCostLe.lean) — the cost of one set of `SetBasedNet.verify` asserted as the proof counts it, a candidate and a check per row of `A`, the enclosure at `SetBasedNet.forwardCost`, and proved at most `(cNeuron + cEval + 21) κ Q³ + (60 + 2R + iterFM (17R + 19)) ξ p Q²` for `Q` at least the output generators and every width, the input's included, `1 ≤ p ≤ Q`, `ξ ≥ 1` and at most `R` split rows per piece | `underspecified` — "with respect to `κ`, `p`, `q` and `ξ`" leaves the widths and the constants open: the proof's `O(κ q³)` is Koller et al. 2025, Prop. 16's `O(n_max² q κ)` with `n_max ≤ q`, which needs every width, `n₀` and `n_κ` included, at most `q`. The proof counts one candidate and one check of `Φ`, where Sec. 4 (and CORA) try one per row of `A`, `p` evaluations at `O(κ q²)` each, inside `O(κ q³)` only for `p ≤ q`; and the constants depend on the per-neuron costs, the split's rows and the passes of Prop. 3; see Findings |
| `Cor. 1` | For `Φ`, `X` and `U = ⟨A, b⟩_H`, the refinement of Prop. 2 decides verification and falsification: `Φ(X\|_{C≤d}) ∩ U = ∅ ⟺ Φ(X) ∩ U = ∅` and `(∃ x ∈ X\|_{C≤d}: Φ(x) ∈ U) ⟺ (∃ x ∈ X: Φ(x) ∈ U)`. | [`EncloseUnsafeInputsSound.lean`](../../src/CORALean/NN/Theorems/EncloseUnsafeInputsSound.lean) — `SetBasedNet.encloseUnsafeInputs_sound`, both equivalences | `underspecified` — as at `Prop. 2`, from which it follows: the approximation errors pointwise; `X` is only "an input set" in the statement and a zonotope in Prop. 2; see Findings |
| `Eq. 14` | `y = c_y + G_y β` for some `β ∈ B_{q_κ}`, in the proof of Prop. 2. | n/a — a step of the proof of `Prop. 2` | `not-a-claim` |
| `Eq. 15` | `Φ(X ∖ X\|_{C≤d}) ∩ U = ∅` and `¬(∃ x ∈ X ∖ X\|_{C≤d}: Φ(x) ∈ U)`, in the proof of Cor. 1. | n/a — a step of the proof of `Cor. 1` | `not-a-claim` |
| `Sec. 5` | The evaluation: CORA against the top-5 tools of VNN-COMP'24 on eight benchmarks (Tab. 1), and the ablations on the input refinement, the GPU and batch size and the falsification (Tabs. 2, 3), with the hardware, benchmarks and termination of App. A, the heuristics of Tab. 4 and the results of App. C (Tab. 5) and Tab. 6. | n/a — experiments | `not-a-claim` |
| `App. A` | The refinement is stopped after 8 iterations of Prop. 2 per iteration of Alg. 1, each with at most 4 passes of Prop. 3; counterexamples are checked at the VNN-COMP tolerance. | n/a — the evaluation's settings; the passes of Prop. 3 are `ConZonotope.fourierMotzkinIter`'s `k` | `not-a-claim` |

## Findings

**`Sec. 3`, `Prop. 2` and `Cor. 1` — the latent space needs pointwise errors.** The proof of Prop. 2
starts from `Φ(x) = c_y + G_y β` with "the first `q₀` factors of the output `y` are the factors of
the input `x`". That is a property of how `Y` was computed, not of `Y` enclosing `Φ(X)`: Prop. 2
calls `Y` "an enclosure of the output set", and Prop. 1 guarantees no more than
`L_k(H_{k-1}) ⊆ enclose(L_k, H_{k-1})` per layer. For the activation `ϕ(t) = -t` with slope `1` and
errors `[0, 0]` on `X = ⟨0, [1]⟩_Z`, `enclose` returns `⟨0, [1 0]⟩_Z = [-1, 1] ⊇ ϕ(X)`, yet the
output factor of `ϕ(β)` is `-β`; for `U = {y ≥ ½}`, `C = [-1]` and `d = -½` give
`X|_{C≤d} = [½, 1]`, which misses the unsafe input `-1`
([`EncloseUnsafeInputs.lean`](../../src/CORALean/NN/Counterexamples/EncloseUnsafeInputs.lean)). What
the proof uses is that each approximation error bounds `ϕ(t) - m t` at every `t` the neuron's input
takes, as the errors of Koller et al. 2025, Def. 6 do; then
`ϕ(h(i)) = m h(i) + ½(e̲ + ē) + γ(i) ½(ē - e̲)` for some `γ(i) ∈ [-1, 1]`, a new factor beside the
input's ([`ForwardLatent.lean`](../../src/CORALean/NN/Theorems/ForwardLatent.lean)). The
formalization assumes exactly that (`SetBasedNet.IsRelaxationOf`).

****`Sec. 3`, `Cor. 1` — the hypercube and the corollary.**.** The hypercube does not "remain
unchanged", as `Sec. 3` says: it gains a dimension per neuron, and only its first `q₀` coordinates
are the input's. `Cor. 1` is stated for an arbitrary input set `X` and follows from Prop. 2, so it
carries the same hypothesis and needs `X` a zonotope.

**`Eq. 9` — the sign of the falsification vertex.** `U = ⟨A, b⟩_H = {y | A y ≤ b}`, so the point of
`Y` most likely in `U` along row `i` minimizes `A(i,·) y`, at `β̃ = -sign(A(i,·) G_y)`. The printed
`β̃ᵢ = sign(A(i,·) G_y)` is the support point in direction `A(i,·)ᵀ` (Althoff and Frehse 2016,
Lemma 1), the vertex farthest from the halfspace. For `Y = ⟨0, [1]⟩_Z` and `U = {y ≤ 0}`,
`Y ∩ U = [-1, 0]` and the printed `ỹ = 1` is not in `U`, let alone on the boundary of `Y ∩ U`
([`SignBoundaryPoint.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/SignBoundaryPoint.lean)).
CORA's `verify.m` (`'zonotack'`, "the vertex that minimizes the distance to each halfspace") takes
`beta_ = -sign(...)` and reverses it for safe-set specifications. With `-sign`, `ỹ` attains the
least `A(i,·) y` over `Y`, so it satisfies row `i` whenever any point of `Y` does; for one row,
`ỹ ∈ Y ∩ U` whenever `Y ∩ U ≠ ∅`
([`ZonotackFactorsIsLeast.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ZonotackFactorsIsLeast.lean)).
Alg. 1, line 10 has the same sign.

**`Prop. 3` and `Eq. 13` — the two readings of `A⁻`.** App. D defines `A⁺ = ½(A + |A|) ∈ ℝ_{≥0}` and
"the matrix `A⁻ ∈ ℝ_{≥0}` analogously". The minimum of `C(i,·) Σ_{∖{j}} β̃` over the box is
`C⁺(i,·) Σ_{∖{j}} β̲₀ + C⁻(i,·) Σ_{∖{j}} β̄₀` for `C⁻ = ½(C - |C|)`, the entries `≤ 0`, and
`C⁺(i,·) Σ_{∖{j}} β̲₀ - C⁻(i,·) Σ_{∖{j}} β̄₀` for `C⁻ = ½(|C| - C) ≥ 0`. Prop. 3 and its proof write
`d(i) - C⁺(…) β̲₀ - C⁻(…) β̄₀`, which is right for the first; Eq. 13 writes
`c ⊕ [G⁺ β̲ - G⁻ β̄, G⁺ β̄ - G⁻ β̲]`, which is right for the second. Under either reading one of the
two is wrong.

****`Prop. 3` — the formalization and CORA.**.** The formalization takes `C⁻ = ½(C - |C|)`, under
which Prop. 3 holds as printed
([`FourierMotzkinBoundsOuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/FourierMotzkinBoundsOuter.lean)),
and Eq. 13 becomes `c ⊕ [G⁺ β̲ + G⁻ β̄, G⁺ β̄ + G⁻ β̲]`
([`IntervalOfFactorBoundsOuter.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/IntervalOfFactorBoundsOuter.lean));
as printed it fails on `Z = ⟨0, [-1]⟩_Z`, whose bounds `[-1, 1]` give the empty interval from `1` to
`-1`
([`IntervalOfFactorBoundsPrinted.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Counterexamples/IntervalOfFactorBoundsPrinted.lean)).
CORA is right both times: `aux_fourierMotzkinApproximation` multiplies each entry by the lower bound
where it is positive and the upper where negative, and `aux_boundConZonotope` maps the factor box by
its center and radius, `c + G β_c ± |G| β_r`. The proof's last sentence sets `β̄(j)` to the "minimum
lower bound", meaning the minimum upper bound.

**`Prop. 4` — what the `O` is in.** The bound is "with respect to `κ`, `p`, `q`, and `ξ`", and the
proof absorbs into it `O(p n_κ q)` for the test (8), `O((n₀ + n_κ) q)` for a candidate and
`O(κ q² + p n_κ)` for its check, and cites Koller et al. 2025, Prop. 16 for the enclosure at
`O(κ q³)`, which states `O(n_max² q κ)`. Each step needs a width at most `q`; with `n_max` over the
layers only, a network with a wide input layer and few generators is already beyond it (the
`Prop. 16` finding of that paper). The proof also counts one candidate (Alg. 1, line 10, one
`β̃_i`), where Sec. 4 computes one per row of `A` and CORA tries all `p`: then the checks cost
`O(p κ q²)`, inside `O(κ q³ + ξ p q²)` only when `p ≤ q`. The formalization asserts the cost of one
set of `SetBasedNet.verify` per operation, with a cost per neuron for the enclosure's slopes and
errors and for `ϕ` at a point. It proves the printed form for `Q` covering every width and the
output generators, `p ≤ Q`, `ξ ≥ 1` and at most `R` split rows per piece, with constants in those
costs, `R` and the passes of Prop. 3
([`VerifyStepCostLe.lean`](../../src/CORALean/NN/Complexity/Time/Theorems/VerifyStepCostLe.lean)).

**`Alg. 1` — the listing.** Line 10 computes one candidate `β̃_i = sign(A(i,·) G_y)` with `i` the
iteration counter of line 2, where Sec. 4 and CORA try one per row of `A`, and with the sign of
`Eq. 9`; line 11 evaluates `Φ(x)` for `Φ(x̃_i)`. Line 15 computes the constraints of Prop. 2 for
`X_i`, which from the second iteration on is a constrained zonotope `X_i|_{C_j≤d_j}` (line 16),
while Prop. 2 and Prop. 1 are stated for a zonotope; App. D resolves it, storing "only the bounds
of the constrained zonotopes in the queue", which `SetBasedNet.verify` does: each piece is bounded
by Prop. 3 and stored as `X_i` rescaled to that factor box, as CORA's `aux_refineInputSet` does by
`aux_scaleAndOffsetZonotope`. The loop as printed need not end; CORA stops at
`options.nn.max_verif_iter` or the timeout with `UNKNOWN`, the budget of `SetBasedNet.verify`.
CORA's `aux_refineInputSet` also iterates Prop. 2 (`options.nn.refinement_max_iter`, App. A's 8
iterations), re-propagating the rescaled set; one refinement per set is what the listing prints
and what the formalization does. Soundness holds for any split that covers the factor box
([`IsVerifySound.lean`](../../src/CORALean/NN/Theorems/IsVerifySound.lean)).
