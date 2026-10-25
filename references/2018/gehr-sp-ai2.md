# AI2: Safety and Robustness Certification of Neural Networks with Abstract Interpretation

```bibtex
@inproceedings{gehr2018ai,
  author = {Gehr, T. and Mirman, M. and Drachsler-Cohen, D. and Tsankov, P. and Chaudhuri, S. and Vechev, M.},
  title = {AI2: Safety and Robustness Certification of Neural Networks with Abstract Interpretation},
  booktitle = {2018 IEEE Symposium on Security and Privacy (SP)},
  year = {2018}
}
```

**Source:** https://files.sri.inf.ethz.ch/website/papers/sp2018.pdf  
**Inventory:** confirmed

Abstract interpretation of a network written as conditional affine transformations: the
abstract transformer of every CAT function, built from a domain's affine map, meet and join,
and its soundness. `Cat`, `CatDomain` and `Cat.transformer`; CORA cites the paper for its
convolution and pooling layers.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Fig. 3` | (§II, CAT functions) `f(x) ::= W·x + b \| case E₁: f₁(x), …, case E_k: f_k(x) \| f(f′(x))` with `E ::= E ∧ E \| xᵢ ≥ xⱼ \| xᵢ ≥ 0 \| xᵢ < 0`; a case function returns `fᵢ(x)` for the first `Eᵢ` satisfied by `x` | [`Cat.lean`](../../src/CORALean/NN/Definitions/Cat.lean) — weights stored in a scalar `𝕋` and read through `toReal`; evaluation is a relation, a point no guard accepts having no value | `correct` |
| `Sec. II (ReLU to CAT)` | (§II) `ReLU = ReLUₙ ∘ … ∘ ReLU₁` with `ReLUᵢ(x) = case (xᵢ ≥ 0): x, case (xᵢ < 0): I_{i←0}·x` | [`CatReluOn.lean`](../../src/CORALean/NN/Operations/CatReluOn.lean), [`CatReluOnEvalIff.lean`](../../src/CORALean/NN/Theorems/CatReluOnEvalIff.lean) — `Cat.reluOn_finRange_eval_iff`: the composition maps `x` to `max(x, 0)` and to nothing else; the chain starts from an identity affine map, which the paper does not write | `correct` |
| `Sec. II (Conv to CAT)` | (§II, Appendix A) a convolutional layer `Conv_F` equals the fully connected layer `FC_{W^F, b^F}` after reshaping, `W^F`'s entries `Σ W^k_{i′j′k′} · [l = n·r·(i+i′−2) + r·(j+j′−2) + k′]` and `b^F` copies of the filter biases | [`Conv.lean`](../../src/CORALean/NN/Layers/Operations/Conv.lean), [`TapMatMulVec.lean`](../../src/CORALean/NN/Layers/Theorems/TapMatMulVec.lean) — the convolution is `Layer.linear` at a stencil matrix, and `tapMat_mulVec` is that row `j` times `x` is the sum over the row's taps, for any injective stencil; the paper's index map `n·r·(i+i′−2) + …` is one such stencil and is not instantiated, nor its reshaping order | `correct` |
| `Sec. II (MaxPool to CAT)` | (§II, Appendix A) `MaxPool′_{p,q} = f_{(m/p)(n/q)r} ∘ … ∘ f₁ ∘ f^MP`: `f^MP` the permutation `W^MP` bringing each `p × q` block together, `fᵢ` the case function `case (x_k ≥ all others in the segment): W^{(i,k)}·x` replacing the `p·q` values of segment `i` by their maximum | [`CatMaxSegment.lean`](../../src/CORALean/NN/Operations/CatMaxSegment.lean), [`CatMaxSegments.lean`](../../src/CORALean/NN/Operations/CatMaxSegments.lean), [`CatMaxPool.lean`](../../src/CORALean/NN/Operations/CatMaxPool.lean), [`CatMaxSegmentEvalIff.lean`](../../src/CORALean/NN/Theorems/CatMaxSegmentEvalIff.lean), [`CatMaxSegmentsEvalIff.lean`](../../src/CORALean/NN/Theorems/CatMaxSegmentsEvalIff.lean), [`CatMaxPoolEvalIff.lean`](../../src/CORALean/NN/Theorems/CatMaxPoolEvalIff.lean) — `Cat.maxPool_eval_iff`: the composition maps `x` to the window maxima and to nothing else. Windows are any stencil (`f^MP` a selection, a permutation when the windows partition the input); each step is framed by affine identity maps renaming `a + (k+1)(r+1)` to `a + (k+1) + (k+1)r` coordinates, which the paper's index arithmetic does silently; each guard also compares `x_k` with itself (see Findings) | `underspecified` — Appendix A ranges `i` over `m/p · n/p · r` segments where `m/p · n/q · r` are meant |
| `Sec. III (transformers)` | (§III) the concrete transformer `T_f(X) = {f(x) \| x ∈ X}`; an abstract transformer `T#_f` is sound if `T_f(γ(a)) ⊆ γ(T#_f(a))` for all `a` | [`Cat.lean`](../../src/CORALean/NN/Definitions/Cat.lean), [`CatDomain.lean`](../../src/CORALean/NN/Definitions/CatDomain.lean) — `Cat.image` is `T_f`; `γ` is a representation's `construct`, and `CatDomain.IsSound` asks this inclusion of `Aff`, `⊓` and `⊔` | `correct` |
| `Sec. IV-A (Aff)` | (§IV-A) for Zonotope and Polyhedra, the operator `Aff` abstracting `f(x) = W·x + b` is supported and exact | [`AffineExact.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/AffineExact.lean), [`ExistsConstructEqImageAffine.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/ExistsConstructEqImageAffine.lean) — an equality for zonotopes (`mtimes` then `plus` with the point `b`); for polyhedra, possibly unbounded, an existence theorem through Fourier–Motzkin, as no elimination is computed | `correct` |
| `Sec. IV-A (meet)` | (§IV-A) the meet of a zonotope with a linear constraint can be computed by modifying the intervals of the error terms, [11] | n/a — restated from [11] (Ghorbal, Goubault, Putot, CAV 2009), which this repository has no page for; `CatDomain` takes the meet as a parameter | `restated` |
| `Fig. 8` | (§IV-A) abstract transformers for CAT functions: `T#_f(a) = Aff(a, W, b)`; `T#_f(a) = ⊔_{1≤i≤k} T#_{fᵢ}(a ⊓ Eᵢ)`; `T#_f(a) = T#_{f₂}(T#_{f₁}(a))` | [`CatTransformer.lean`](../../src/CORALean/NN/Operations/CatTransformer.lean) — the join over the cases folded from `⊥`, right to left | `correct` |
| `Thm. 1` | (§IV-A) for any CAT function `f` and any abstract input `a ∈ Aᵐ`, `T_f(γᵐ(a)) ⊆ γⁿ(T#_f(a))`, given sound `Aff`, meet and join | [`CatTransformerOuter.lean`](../../src/CORALean/NN/Theorems/CatTransformerOuter.lean) — `Cat.transformer_outer` | `correct` |
| `Sec. IV-B (robustness)` | (§IV-B) `γⁿ(T#_N(αᵐ(X))) ⊆ C` suffices to prove that `N` satisfies the robustness property `(X, C)` | [`CatImageSubsetOfTransformer.lean`](../../src/CORALean/NN/Theorems/CatImageSubsetOfTransformer.lean) — `α(X)` is any abstract element whose concretization contains `X` | `correct` |
| `Sec. IV-B (containment)` | (§IV-B) for `C = ⋀ᵢ ⋁ⱼ l_{ij}` with linear literals, `γ(a) ⊆ C` follows from `a ⊓ ⋀ⱼ ¬l_{ij} = ⊥` for all `i` | [`SubsetCnfOfMeetEqBot.lean`](../../src/CORALean/NN/Theorems/SubsetCnfOfMeetEqBot.lean) — literals of any kind with a complementing negation, so linear ones among them | `correct` |
| `Sec. V` | (§V) the implementation: Apron's Box, Zonotope and Polyhedra domains, and bounded powersets joining their two closest elements until at most `N` remain | n/a — not a claim: a description of the implementation, whose soundness is `Thm. 1`'s hypothesis on the domain | `not-a-claim` |
| `Sec. VI-A (ℓ∞)` | (§VI-A) the inputs perturbed by an `ℓ∞` attack, a box, are captured exactly by a single zonotope | [`IntervalZonotopeContains.lean`](../../src/CORALean/ContSet/Conversion/Real/Theorems/IntervalZonotopeContains.lean) — `Interval.zonotope_exact`, for every nonempty box | `correct` |
| `Sec. VI` | (§VI) evaluation on MNIST and CIFAR networks: precision and running time of Box, Zonotope and bounded powersets, and comparison with Reluplex | n/a — not a claim: experiments | `not-a-claim` |
| `Sec. VII` | (§VII) comparison of defended networks by provable robustness | n/a — not a claim: experiments | `not-a-claim` |

## Findings

**AI2, `MaxPool′` as a CAT function.** Two misprints in the indices, neither touching the
construction: Appendix A lets `i` range over `1 ≤ i ≤ m/p · n/p · r` segments, where the image
has `m/p · n/q · r` blocks, and §II's `fᵢ(x) = (x₁, …, x_{i−1}, x_k, x_{i+p·q}, …,
x_{m·n−(p·q−1)·(i−1)})` drops the depth `r` (the section's example has `r = 1`). The guard of
the `k`-th case is the conjunction of `x_k ≥ x_{k′}` over the other `k′` of the segment; at
`p·q = 1` that conjunction is empty, which the grammar of `Fig. 3` has no form for, so the
formalization includes the always-true `x_k ≥ x_k`. [`CatMaxSegment.lean`](../../src/CORALean/NN/Operations/CatMaxSegment.lean), [`CatMaxPoolEvalIff.lean`](../../src/CORALean/NN/Theorems/CatMaxPoolEvalIff.lean)
