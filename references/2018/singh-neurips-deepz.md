# Fast and Effective Robustness Certification

```bibtex
@inproceedings{singh2018fast,
  author = {Singh, G. and Gehr, T. and Mirman, M. and Püschel, M. and Vechev, M.},
  title = {Fast and Effective Robustness Certification},
  booktitle = {Advances in Neural Information Processing Systems},
  year = {2018}
}
```

**Source:** https://papers.nips.cc/paper_files/paper/2018/file/f2f446980d8e971ef3da97af089481c3-Paper.pdf  
**Inventory:** confirmed

DeepZ: pointwise zonotope transformers for ReLU, sigmoid and tanh of least area in the
input-output plane. `Real.deepZRelu`, which at ℝ is the tree's `reluRelaxation reluSlope`, and
`Real.deepZSShape`, which is CORA's `'singh'` polynomial of order 1.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | (§2) the zonotope abstraction: an affine form `x̂ = α₀ + Σᵢ αᵢ εᵢ` per variable, `εᵢ ∈ [aᵢ, bᵢ] ⊆ [-1, 1]` shared between variables | n/a — restated from [11] (Ghorbal, Goubault, Putot, CAV 2009), with each `εᵢ` ranging over a subinterval of `[-1, 1]`; at `[aᵢ, bᵢ] = [-1, 1]` the zonotope is tracked as `Def. 1` on [Reachability of Uncertain Linear Systems Using Zonotopes](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 2` | (§2) the interval affine form `x̂ = [α₀, β₀] + Σᵢ [αᵢ, βᵢ] εᵢ`, its interval arithmetic rounded outward, for soundness under floating point | n/a — done differently: a float set stores point coefficients and pays its rounding into an error box (`InflatedContSet`); [the coverage README, departures from CORA](../coverage/README.md#departures-from-cora-that-belong-to-no-single-method) | `done-differently` |
| `Sec. 2 (Aff)` | (§2) affine arithmetic is fast and exact for affine transformations, [10] | n/a — restated from AI2, tracked as `Sec. IV-A (Aff)` on [AI2: Safety and Robustness Certification of Neural Networks with Abstract Interpretation](gehr-sp-ai2.md) | `restated` |
| `Sec. 2 (robustness)` | (§2) a robustness property `(R_{x,ε}, C_L)` holds if the abstract output of an abstraction of `R_{x,ε}` is included in `C_L` | n/a — restated from AI2, tracked as `Sec. IV-B (robustness)` on [AI2: Safety and Robustness Certification of Neural Networks with Abstract Interpretation](gehr-sp-ai2.md) | `restated` |
| `Fig. 1` | (§3.1) for `l < 0 < u`, the parallelograms between `ŷ = λ x̂` and `ŷ = λ x̂ + u (1 - λ)` for `0 ≤ λ ≤ u / (u - l)`, and between `ŷ = λ x̂` and `ŷ = λ (x̂ - l)` for `u / (u - l) ≤ λ ≤ 1`, are sound for ReLU | [`ReluBoundsOfSlope.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ReluBoundsOfSlope.lean), [`ReluGapOfSlopeEqIte.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ReluGapOfSlopeEqIte.lean) — ReLU lies between `λ t` and `λ t + reluGapOfSlope λ l u` for every `λ ∈ [0, 1]`, and the gap is `u (1 - λ)` below the secant slope and `-λ l` above it | `correct` |
| `Eq. 3` | (§3.1) the area of Fig. 1 (a)'s parallelogram, `A₁(λ) = (1 - λ) u (u - l)`, decreases in `λ` and is least at `λ = u / (u - l)` | [`ReluGapOfSlopeEqIte.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ReluGapOfSlopeEqIte.lean), [`ReluBandAreaLe.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ReluBandAreaLe.lean) — `A₁` is the gap times `u - l`; least at the secant by `relu_band_area_le`, which bounds every sound band, of either family | `correct` |
| `Eq. 4` | (§3.1) the area of Fig. 1 (b)'s parallelogram, `A₂(λ) = λ (-l) (u - l)`, increases in `λ` and is least at `λ = u / (u - l)` | [`ReluGapOfSlopeEqIte.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ReluGapOfSlopeEqIte.lean), [`ReluBandAreaLe.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ReluBandAreaLe.lean) — as for `Eq. 3` | `correct` |
| `Thm. 3.1` | (§3.1) among the pointwise zonotope approximations `O` altering only `ŷ`, the one of least area in the xy-plane is Eq. (5): `ŷ = x̂` if `l > 0`, `[0, 0]` if `u ≤ 0`, otherwise `[λl, λu] x̂ + [μl, μu] + [μl, μu] ε_new` with `λ = u / (u - l)`, `μ = -u l / (2 (u - l))` rounded outward | [`DeepZRelu.lean`](../../src/CORALean/NN/Layers/Definitions/DeepZRelu.lean), [`DeepZReluEq.lean`](../../src/CORALean/NN/Layers/Theorems/Real/DeepZReluEq.lean), [`DeepZReluEncloses.lean`](../../src/CORALean/NN/Layers/Theorems/Real/DeepZReluEncloses.lean), [`ReluBandAreaLe.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ReluBandAreaLe.lean) — over ℝ: Eq. (5) is `reluRelaxation reluSlope` (whose soundness `reluRelaxation_encloses` holds at every float scalar too), it is sound, and no band `λ t + c ≤ ReLU(t) ≤ λ t + d` of any slope has less area. The outward-rounded interval coefficients are done differently (`Eq. 2`) | `underspecified` — `O` is not defined beyond Fig. 1's parallelograms; formalized over the bands of every slope |
| `Fig. 2` | (§3.2) for the sigmoid, the parallelogram between the lines of slope `λ` through `(l, σ(l))` and `(u, σ(u))` is sound for `0 ≤ λ ≤ min(σ′(l), σ′(u))` | [`SShapeBandSound.lean`](../../src/CORALean/NN/Layers/Theorems/Real/SShapeBandSound.lean), [`DeepZSShapeSigmoidEncloses.lean`](../../src/CORALean/NN/Layers/Theorems/Real/DeepZSShapeSigmoidEncloses.lean) — `sShape_band_sound` for every `λ ≤ min(f′(l), f′(u))` (no lower bound needed) at any `f` whose derivative rises and then falls, which `deepZSShape_sigmoid_encloses` discharges for `σ` | `correct` |
| `Eq. 6` | (§3.2) the area `A(λ) = (σ(u) - σ(l) - λ (u - l)) (u - l)` decreases in `λ` and is least at `λ_opt = min(σ′(l), σ′(u))` | [`SShapeBandAreaLe.lean`](../../src/CORALean/NN/Layers/Theorems/Real/SShapeBandAreaLe.lean) — every sound band of the family has `λ ≤ min(f′(l), f′(u))`, so none has less area than `λ_opt`'s; for any differentiable `f` | `correct` |
| `Thm. 3.2` | (§3.2) for a smooth S-shaped `f` (footnote: `f′ ≥ 0` and `f″(x) ≤ 0 ⇔ x ≤ x′`), among the pointwise approximations with box `[f(l), f(u)]`, the one of least area is Eq. (7): `[f(u)]` if `l = u`, otherwise `λ x̂ + μ₁ + μ₂ ε_new` with `λ = min(f′(l), f′(u))`, `μ₁ = (f(u) + f(l) - λ (u + l)) / 2`, `μ₂ = (f(u) - f(l) - λ (u - l)) / 2`, rounded outward | [`IsSShapedPrinted.lean`](../../src/CORALean/NN/Layers/Definitions/IsSShapedPrinted.lean), [`DeepZSShape.lean`](../../src/CORALean/NN/Layers/Definitions/DeepZSShape.lean), [`DeepZSShapeCubeNotEncloses.lean`](../../src/CORALean/NN/Layers/Theorems/Real/DeepZSShapeCubeNotEncloses.lean), [`DeepZSShapeEncloses.lean`](../../src/CORALean/NN/Layers/Theorems/Real/DeepZSShapeEncloses.lean), [`SShapeBandAreaLe.lean`](../../src/CORALean/NN/Layers/Theorems/Real/SShapeBandAreaLe.lean), [`SShapeUnimodal.lean`](../../src/CORALean/NN/Layers/Theorems/SShapeUnimodal.lean) — over ℝ. As printed false: `x³` is S-shaped by the footnote and Eq. (7) misses it on `[-1, 2]` (`deepZSShape_cube_not_encloses`). Sound once `f″ ≥ 0` left of `x′` and `≤ 0` right of it (`deepZSShape_encloses`, stated as `f′` rising then falling), and least in area (`sShape_band_area_le`) **Counterexample:** `deepZSShape_cube_not_encloses` | `fixed` — the footnote's S-shape has the curvature reversed; true with `f″(x) ≥ 0 ⇔ x ≤ x′` |
| `Sec. 3.3` | (§3.3) tanh is S-shaped, and Thm. 3.2 gives its transformer with `f′(x) = 1 - tanh²(x)` | [`DeepZSShapeTanhEncloses.lean`](../../src/CORALean/NN/Layers/Theorems/Real/DeepZSShapeTanhEncloses.lean) — `deepZSShape_tanh_encloses`, the derivative `1 - tanh²` identified through `tanh t = 2 σ(2t) - 1` | `correct` |
| `Sec. 4` | (§4) evaluation of DeepZ against AI2 and Fast-Lin on MNIST and CIFAR10 networks, undefended and defended | n/a — not a claim: experiments | `not-a-claim` |
| `Sec. 4.1 (ℓ∞)` | (§4.1) the perturbation region `R_{x,ε}` of an `ℓ∞` attack is exactly one zonotope | n/a — restated from AI2, tracked as `Sec. VI-A (ℓ∞)` on [AI2: Safety and Robustness Certification of Neural Networks with Abstract Interpretation](gehr-sp-ai2.md) | `restated` |

## Findings

**DeepZ's S-shaped functions.** The footnote to `Thm. 3.2` defines a smooth `f` as S-shaped when
`f′ ≥ 0` and `f″(x) ≤ 0 ⇔ x ≤ x′`: concave left of `x′` and convex right of it. The sigmoid is
the other way round, convex left of `0`, and is not S-shaped by this definition, while `x³` is,
with `x′ = 0`. On `[-1, 2]` Eq. (7) gives `λ = min(3, 12) = 3`, `μ₁ = 2`, `μ₂ = 0`, the line
`3x + 2` of no width, and `f(1) = 1` lies `4` below it: the soundness range
`0 ≤ λ ≤ min(f′(l), f′(u))` the proof relies on (`Fig. 2`) needs `f′` to stay above its smaller
end value on the box, which a derivative falling to `x′` and rising after it does not. With the
inequality reversed, `f″(x) ≥ 0 ⇔ x ≤ x′`, the derivative rises to `x′` and falls after it, the
band is sound, and its area is least among the family. The theorem also writes the box as
`l_y = σ(l_x)`, `u_y = σ(u_x)` for a general `f`. `Thm. 3.1`'s class `O` of approximations
"altering only `ŷ`" is wider than Fig. 1's parallelograms — `ŷ` may use every noise symbol of
`x̂` — and the argument ranges over the parallelograms only, which is what is formalized.
[`DeepZSShapeCubeNotEncloses.lean`](../../src/CORALean/NN/Layers/Theorems/Real/DeepZSShapeCubeNotEncloses.lean), [`DeepZSShapeEncloses.lean`](../../src/CORALean/NN/Layers/Theorems/Real/DeepZSShapeEncloses.lean), [`ReluBandAreaLe.lean`](../../src/CORALean/NN/Layers/Theorems/Real/ReluBandAreaLe.lean)
