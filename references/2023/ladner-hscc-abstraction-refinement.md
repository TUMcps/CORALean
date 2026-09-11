# Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis

T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network
Verification using Sensitivity Analysis". HSCC 2023.

**Source:** https://mediatum.ub.tum.de/doc/1710698/1710698.pdf (PDF; custom-embedded-font glyph codes decoded via the PDF's own ToUnicode CMaps)  
**Inventory:** confirmed

Refining a network's abstraction where it is loose, guided by a sensitivity
analysis. `NN.RefinableNetwork`, the schedule, and the theorems that say
refining only tightens.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 2.1` | (Layers of Neural Networks, [6, Sec. 5.1]) layer operation L_k: R^{n_{k-1}} to R^{n_k} via weight matrix, bias, and elementwise activation | — |
| `Def. 2.2` | (Neural Networks, [6, Sec. 5.1]) network as κ alternating layers, h0=x, h_k=L_k(h_{k-1}), y=h_κ, Eq. (2) | — |
| `Def. 2.3` | (Neuron Sensitivity, [40]) sensitivity S_k of layer k on output y w.r.t. input h_{k-1}, via chain rule of Jacobians/derivatives, Eq. (3) | [`Sensitivity.lean`](../../src/CORALean/NN/Operations/Sensitivity.lean), [`LayerSensitivity.lean`](../../src/CORALean/NN/Operations/LayerSensitivity.lean) |
| `Def. 2.4` | (Polynomial Zonotope, [24]) offset c, dependent generators G, exponent matrix E, independent generators G_I | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Prop. 2.6` | (Zonotope Enclosure, [23, Prop. 3.1.14]) PZ enclosed by Z=zonotope(PZ), Eq. (8) | — |
| `Def. 2.5` | (Zonotope, [12, Def. 1]) center c and generator matrix G, Eq. (7) | n/a — restated from A. Girard, "Reachability of Uncertain Linear Systems Using Zonotopes", HSCC 2005, where the representation is introduced |
| `Prop. 2.7` | (Interval Enclosure, [1, Prop. 2.2]) interval bounds [l,u] of a zonotope, Eq. (9) | — |
| `Prop. 2.8` | (Linear Map, [23, Prop. 3.1.18/19]) linear map of a polynomial zonotope, Eq. (10) | — |
| `Prop. 2.9` | (Quadratic Map, [23, Prop. 3.1.30]) standard quadratic map sq(PZ1,PZ2) of two polynomial zonotopes, Eq. (11) | — |
| `Prop. 2.10` | (Polynomial Map, [23, Prop. A.1]) polynomial map poly(PZ,o) of order o via repeated quadratic maps, Eq. (12) | [`Mul.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Mul.lean) |
| `Prop. 2.11` | (Projection, [23, Prop. 3.1.16]) projection of a polynomial zonotope on dimension i, Eq. (13) | — |
| `Prop. 2.12` | (Cartesian Product, [25, Prop. 2]) Cartesian product of two polynomial zonotopes with common identifier vector, Eq. (14) | — |
| `Prop. 2.13` | (Order Reduction, [23, Prop. 3.1.39]) reduce(PZ,o') returns a polynomial zonotope of order ≤ o' enclosing PZ, Eq. (15) | n/a — restated; tracked as `Prop. 16` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Prop. 2.14` | (Image Enclosure, [25, Sec. 3]) H_k = enclose(L_k, H_{k-1}) is an over-approximative output set, Eq. (17); linear layers via Prop. 2.8, nonlinear via Alg. 1 | — |
| `Prop. 3.2` | (sort) sorting the exponent matrix columns of a regular polynomial zonotope lexicographically, Eq. (21) | — |
| `Prop. 3.3` | (merge) merging equal columns of a sorted non-regular polynomial zonotope in O(pn) | — |
| `Prop. 3.4` | (sortPlus) Minkowski sum of m sorted polynomial zonotopes with a common identifier vector, Eq. (22) | — |
| `Prop. 3.5` | (Efficient Polynomial Evaluation) Alg. 2 computes a sound polynomial evaluation p(PZ) in O(pn·o(log n + log o)) | — |
| `Alg. 1` | (§2) Image enclosure for a nonlinear layer k, cites [25] | [`PolyRelaxation.lean`](../../src/CORALean/NN/Layers/PolyRelaxation.lean) |
| `Alg. 2` | (§3) Efficient Polynomial Evaluation | — |
| `Prop. 4.2` | (§4.1, Reuse of Bounds) reused input bounds from a prior iteration still give a sound enclosure, Eq. (26); proof cites Prop. 2.14 | — |
| `Lemma 4.3` | (§4.2, Number of Generators) number of output generators of enclose(H_{k-1}) is determined by the maximum order in the layer's order pattern ψ_k; proof cites Alg. 1 line 9 and Prop. 2.12 | [`RefineLayer.lean`](../../src/CORALean/NN/Operations/RefineLayer.lean), [`RefinementNeuron.lean`](../../src/CORALean/NN/Operations/RefinementNeuron.lean) |
| `Eq. 23` | (§4.2/4.3) order pattern tuple ψ=(ψ2,ψ4,...,ψκ), ψ_k ∈ N_{≥0}^{n_k}, storing per-neuron approximation-polynomial order | [`ActivationPoly.lean`](../../src/CORALean/NN/Float/Layers/ActivationPoly.lean), [`ActivationPolyRefine.lean`](../../src/CORALean/NN/Float/Layers/ActivationPolyRefine.lean), [`PolyRelaxationPad.lean`](../../src/CORALean/NN/Float/Layers/PolyRelaxationPad.lean), [`ActivationPoly.lean`](../../src/CORALean/NN/Layers/ActivationPoly.lean), [`PolyRelaxationPad.lean`](../../src/CORALean/NN/Layers/PolyRelaxationPad.lean), [`RefinableLayer.lean`](../../src/CORALean/NN/RefinableLayer.lean), [`Schedule.lean`](../../src/CORALean/NN/Schedule.lean) |
| `Eq. 27` | (§4.3) the heuristic value of one neuron, which neuron-wise refinement maximizes. | [`RefinementNeuron.lean`](../../src/CORALean/NN/Operations/RefinementNeuron.lean) |
| `Def. 4.4` | (§4.3, Neuron-wise Refinement) refine all neurons j of the layer k̃ with maximal heuristic value whose heuristic is within a factor W of the max, Eq. (27) | [`Refine.lean`](../../src/CORALean/NN/Operations/Refine.lean), [`RefinementNeuron.lean`](../../src/CORALean/NN/Operations/RefinementNeuron.lean), [`ImageSubsetRefine.lean`](../../src/CORALean/NN/Theorems/ImageSubsetRefine.lean) |
| `Eq. 28` | (§4.3) the heuristic summed over a layer, which layer-wise refinement maximizes. | [`RefineWorst.lean`](../../src/CORALean/NN/Operations/RefineWorst.lean), [`RefinementRank.lean`](../../src/CORALean/NN/Operations/RefinementRank.lean) |
| `Def. 4.6` | (§4.3, Layer-wise Refinement) refine all neuron abstractions of the layer k̃ = argmax_k of the summed heuristic over the layer, Eq. (28) | [`RefineLayer.lean`](../../src/CORALean/NN/Operations/RefineLayer.lean), [`RefineWorst.lean`](../../src/CORALean/NN/Operations/RefineWorst.lean), [`RefinementNeuron.lean`](../../src/CORALean/NN/Operations/RefinementNeuron.lean), [`ImageSubsetRefineLayer.lean`](../../src/CORALean/NN/Theorems/ImageSubsetRefineLayer.lean) |
| `Def. 4.7` | (§4.3, σ-All) heuristic considering all neurons equally beneficial, Eq. (30) | [`RefinementRankAll.lean`](../../src/CORALean/NN/Operations/RefinementRankAll.lean) |
| `Def. 4.8` | (§4.3, σ-Random) heuristic sampled uniformly in [0,1], Eq. (31) | n/a — defined by sampling a random variable, which a deterministic and total formalization cannot express; `refineWorst` already takes an arbitrary caller-supplied ranking, so nothing here depends on it |
| `Def. 4.9` | (§4.3, σ-Approximation Error) heuristic using the approximation error e_k(j), Eq. (32) | [`RefinementRankApproxError.lean`](../../src/CORALean/NN/Operations/RefinementRankApproxError.lean) |
| `Def. 4.10` | (§4.3, σ-Layer Bias) heuristic biasing earlier layers, Eq. (33) | [`RefinementRankLayerBias.lean`](../../src/CORALean/NN/Operations/RefinementRankLayerBias.lean) |
| `Def. 4.11` | (§4.3, σ-Sensitivity) heuristic based on sensitivity analysis via Euclidean norm of S_k(j,·), Eq. (34) | [`RefinementRankSensitivity.lean`](../../src/CORALean/NN/Operations/RefinementRankSensitivity.lean) |
| `Def. 4.12` | (§4.3, σ-Weighted Error) heuristic weighting approximation error by sensitivity, Eq. (35) | [`RefinementRank.lean`](../../src/CORALean/NN/Operations/RefinementRank.lean) |
| `Alg. 3` | (§4, Automatic Abstraction Refinement) main refinement loop over layers/neurons using a heuristic σ | — |
| `Prop. 4.13` | (§4.4, Layer Convergence) for a two-layer network, the output converges to the exact image as the number of iterations/order grows, using Alg. 3 | — |
| `Thm. 4.14` | (§4.4, Network Convergence) Alg. 3 is sound and its over-approximation converges to the exact image as iterations grow, provided the heuristic is proportional to the approximation error | — |

## Findings

**HSCC'23 abstraction refinement.** Minor: (i) convergence needs a Lipschitz bound on every network tail; (ii) sensitivity analysis needs differentiability per layer, and differentiability of the network's evaluation does not suffice. [`EncloseAtInflate.lean`](../../src/CORALean/NN/Theorems/EncloseAtInflate.lean), [`EvalDifferentiable.lean`](../../src/CORALean/NN/Theorems/EvalDifferentiable.lean)

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`Mul.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Mul.lean)
* [`PolyRelaxationOfBracket.lean`](../../src/CORALean/NN/Float/Layers/PolyRelaxationOfBracket.lean)
* [`PolySampling.lean`](../../src/CORALean/NN/Float/Layers/PolySampling.lean)
* [`ActivationPolyRefine.lean`](../../src/CORALean/NN/Layers/ActivationPolyRefine.lean)
* [`PolyConvergence.lean`](../../src/CORALean/NN/Layers/PolyConvergence.lean)
* [`PolyFitConvergence.lean`](../../src/CORALean/NN/Layers/PolyFitConvergence.lean)
* [`PolyRangeConvergence.lean`](../../src/CORALean/NN/Layers/PolyRangeConvergence.lean)
* [`PolyRelaxation.lean`](../../src/CORALean/NN/Layers/PolyRelaxation.lean)
* [`PolySampling.lean`](../../src/CORALean/NN/Layers/PolySampling.lean)
* [`SigmoidLinearSigmoid.lean`](../../src/CORALean/NN/Layers/SigmoidLinearSigmoid.lean)
* [`SigmoidPolyRefine.lean`](../../src/CORALean/NN/Layers/SigmoidPolyRefine.lean)
* [`LayerSensitivity.lean`](../../src/CORALean/NN/Operations/LayerSensitivity.lean)
* [`Sensitivity.lean`](../../src/CORALean/NN/Operations/Sensitivity.lean)
* [`API.lean`](../../src/CORALean/NN/Theorems/API.lean)
* [`LinearConvergent.lean`](../../src/CORALean/NN/Theorems/LinearConvergent.lean)
* [`MultiLayerRefinementConverges.lean`](../../src/CORALean/NN/Theorems/MultiLayerRefinementConverges.lean)
