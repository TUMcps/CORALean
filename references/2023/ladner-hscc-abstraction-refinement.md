# Automatic Abstraction Refinement in Neural Network Verification using Sensitivity Analysis

T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network
Verification using Sensitivity Analysis". HSCC 2023.

**Source:** https://mediatum.ub.tum.de/doc/1710698/1710698.pdf (PDF; custom-embedded-font glyph codes decoded via the PDF's own ToUnicode CMaps)  
**Inventory:** confirmed

Refining a network's abstraction where it is loose, guided by a sensitivity
analysis. `NN.RefinableNetwork`, the schedule, and the theorems that say
refining only tightens. §3's `sort`, `merge`, `sortPlus` and `Alg. 2` are
operations of `PolyZonotope/Real`, beside `PolyZonotope.evalPoly`, which is
Horner's rule and a different route to the same value; of `Alg. 2` what is
proved is that it computes the polynomial and leaves the exponent matrix
sorted, and no generator count or running cost is claimed for it.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 2.1` | (Layers of Neural Networks, [6, Sec. 5.1]) layer operation L_k: R^{n_{k-1}} to R^{n_k} via weight matrix, bias, and elementwise activation | n/a — a preliminary restated from the literature, not a result of this paper |
| `Def. 2.2` | (Neural Networks, [6, Sec. 5.1]) network as κ alternating layers, h0=x, h_k=L_k(h_{k-1}), y=h_κ, Eq. (2) | n/a — a preliminary restated from the literature, not a result of this paper |
| `Def. 2.3` | (Neuron Sensitivity, [40]) sensitivity S_k of layer k on output y w.r.t. input h_{k-1}, via chain rule of Jacobians/derivatives, Eq. (3) | [`Sensitivity.lean`](../../src/CORALean/NN/Operations/Sensitivity.lean), [`LayerSensitivity.lean`](../../src/CORALean/NN/Operations/LayerSensitivity.lean) |
| `Def. 2.4` | (Polynomial Zonotope, [24]) offset c, dependent generators G, exponent matrix E, independent generators G_I | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Prop. 2.6` | (Zonotope Enclosure, [23, Prop. 3.1.14]) PZ enclosed by Z=zonotope(PZ), Eq. (8) | [`PolyZonotope_to_Zonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Zonotope.lean) |
| `Def. 2.5` | (Zonotope, [12, Def. 1]) center c and generator matrix G, Eq. (7) | n/a — restated from A. Girard, "Reachability of Uncertain Linear Systems Using Zonotopes", HSCC 2005, where the representation is introduced |
| `Prop. 2.7` | (Interval Enclosure, [1, Prop. 2.2]) interval bounds [l,u] of a zonotope, Eq. (9) | [`PolyZonotope_to_Interval.lean`](../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Interval.lean) |
| `Prop. 2.8` | (Linear Map, [23, Prop. 3.1.18/19]) linear map of a polynomial zonotope, Eq. (10) | [`Map.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Map.lean) |
| `Prop. 2.9` | (Quadratic Map, [23, Prop. 3.1.30]) standard quadratic map sq(PZ1,PZ2) of two polynomial zonotopes, Eq. (11) | [`Mul.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Mul.lean) |
| `Prop. 2.10` | (Polynomial Map, [23, Prop. A.1]) polynomial map poly(PZ,o) of order o via repeated quadratic maps, Eq. (12) | [`Mul.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Mul.lean) |
| `Prop. 2.11` | (Projection, [23, Prop. 3.1.16]) projection of a polynomial zonotope on dimension i, Eq. (13) | [`Project.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Project.lean), [`ProjectExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ProjectExact.lean) |
| `Prop. 2.12` | (Cartesian Product, [25, Prop. 2]) Cartesian product of two polynomial zonotopes with common identifier vector, Eq. (14) | [`ExactCartProd.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/ExactCartProd.lean), [`ExactCartProdPoint.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ExactCartProdPoint.lean); shares the independent generators too, so it is not the product (see Findings) |
| `Prop. 2.13` | (Order Reduction, [23, Prop. 3.1.39]) reduce(PZ,o') returns a polynomial zonotope of order ≤ o' enclosing PZ, Eq. (15) | n/a — restated; tracked as `Prop. 16` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Prop. 2.14` | (Image Enclosure, [25, Sec. 3]) H_k = enclose(L_k, H_{k-1}) is an over-approximative output set, Eq. (17); linear layers via Prop. 2.8, nonlinear via Alg. 1 | [`Layer.lean`](../../src/CORALean/NN/Layer.lean) |
| `Prop. 3.2` | (sort) sorting the exponent matrix columns of a regular polynomial zonotope lexicographically in O(ph log h), Eq. (21) | [`Sorted.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Sorted.lean), [`Sort.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Sort.lean), [`SortExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SortExact.lean), [`SortSorted.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SortSorted.lean), [`SortPoint.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SortPoint.lean) |
| `Prop. 3.3` | (merge) merging equal columns of a sorted non-regular polynomial zonotope in O(ph) | [`Merge.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Merge.lean), [`MergeExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MergeExact.lean), [`MergePoint.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MergePoint.lean), [`MergeSorted.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MergeSorted.lean), [`MergeColInjective.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MergeColInjective.lean); the result is sorted, not regular (see Findings) |
| `Prop. 3.4` | (sortPlus) Minkowski sum of m sorted polynomial zonotopes with a common identifier vector, Eq. (22) | [`SortPlus.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/SortPlus.lean), [`SortPlusExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SortPlusExact.lean), [`SortPlusPoint.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SortPlusPoint.lean), [`SortPlusSorted.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SortPlusSorted.lean); binary, m operands being it iterated |
| `Prop. 3.5` | (Efficient Polynomial Evaluation) Alg. 2 computes a sound polynomial evaluation p(PZ) that is regular, sorted and has O(h^o) generators, in O(p·h^o·(log h + log o)) | [`EvalPolySortExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/EvalPolySortExact.lean), [`EvalPolySortSorted.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/EvalPolySortSorted.lean); soundness and sortedness only — the generator count and the running cost are not claimed, and regularity fails as at `Prop. 3.3` |
| `Alg. 1` | (§2) Image enclosure for a nonlinear layer k, cites [25] | [`PolyRelaxation.lean`](../../src/CORALean/NN/Layers/PolyRelaxation.lean) |
| `Alg. 2` | (§3) Efficient Polynomial Evaluation | [`PowSort.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/PowSort.lean), [`EvalPolySortTailP.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/EvalPolySortTailP.lean), [`EvalPolySortP.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/EvalPolySortP.lean), [`EvalPolySort.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/EvalPolySort.lean), [`PowSortPoint.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/PowSortPoint.lean), [`EvalPolySortTailPoint.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/EvalPolySortTailPoint.lean); the `m` terms are summed in pairs, not in one `m`-way merge |
| `Prop. 4.2` | (§4.1, Reuse of Bounds) reused input bounds from a prior iteration still give a sound enclosure, Eq. (26); proof cites Prop. 2.14 | [`ActivationPolyOn.lean`](../../src/CORALean/NN/Layers/ActivationPolyOn.lean) |
| `Lemma 4.3` | (§4.2, Number of Generators) number of output generators of enclose(H_{k-1}) is determined by the maximum order in the layer's order pattern ψ_k; proof cites Alg. 1 line 9 and Prop. 2.12 | [`ActivationPoly.lean`](../../src/CORALean/NN/Layers/ActivationPoly.lean); `enclose`'s independent block is always empty, so the closed-form dependent count proved there is the whole generator count |
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
| `Alg. 3` | (§4, Automatic Abstraction Refinement) main refinement loop over layers/neurons using a heuristic σ | [`RefineLoop.lean`](../../src/CORALean/NN/Operations/RefineLoop.lean) |
| `Prop. 4.13` | (§4.4, Layer Convergence) for a two-layer network, the output converges to the exact image as the number of iterations/order grows, using Alg. 3 | [`LinearSigmoid.lean`](../../src/CORALean/NN/Layers/LinearSigmoid.lean), [`LinearSigmoidConverges.lean`](../../src/CORALean/NN/Theorems/LinearSigmoidConverges.lean), [`ExistsScheduleLinearSigmoidSubset.lean`](../../src/CORALean/NN/Theorems/ExistsScheduleLinearSigmoidSubset.lean), [`SigmoidPolyRefine.lean`](../../src/CORALean/NN/Layers/SigmoidPolyRefine.lean), [`LinearConvergent.lean`](../../src/CORALean/NN/Theorems/LinearConvergent.lean) |
| `Thm. 4.14` | (§4.4, Network Convergence) Alg. 3 is sound and its over-approximation converges to the exact image as iterations grow, provided the heuristic is proportional to the approximation error | [`EncloseAtInflate.lean`](../../src/CORALean/NN/Theorems/EncloseAtInflate.lean), [`MultiLayerRefinementConverges.lean`](../../src/CORALean/NN/Theorems/MultiLayerRefinementConverges.lean); carries the Lipschitz hypothesis the printed proof leaves out (see Findings) |

## Findings

**HSCC'23 abstraction refinement.** Minor: (i) convergence needs a Lipschitz bound on every network tail; (ii) sensitivity analysis needs differentiability per layer, and differentiability of the network's evaluation does not suffice; (iii) `Prop. 3.3`'s `merge` joins equal exponent columns and nothing else, so it leaves the all-zero column `Def. 2.4` forbids as well — the result is sorted but not regular in general, though no such column arises in `Alg. 2`; (iv) `Prop. 2.12` writes `PZ₁ × PZ₂ =` for a set that shares the dependent factors *and* the first q₁ independent generators, so it is a subset of the Cartesian product rather than the product — as `Prop. 3.4`'s "Minkowski sum" is a subset of the Minkowski sum, both being pairings at one factor vector. [`EncloseAtInflate.lean`](../../src/CORALean/NN/Theorems/EncloseAtInflate.lean), [`EvalDifferentiable.lean`](../../src/CORALean/NN/Theorems/EvalDifferentiable.lean), [`MergeColInjective.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MergeColInjective.lean), [`ExactCartProdPoint.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ExactCartProdPoint.lean)

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`PolyRelaxationOfBracket.lean`](../../src/CORALean/NN/Float/Layers/PolyRelaxationOfBracket.lean)
* [`PolySampling.lean`](../../src/CORALean/NN/Float/Layers/PolySampling.lean)
* [`ActivationPolyRefine.lean`](../../src/CORALean/NN/Layers/ActivationPolyRefine.lean)
* [`PolyConvergence.lean`](../../src/CORALean/NN/Layers/PolyConvergence.lean)
* [`PolyFitConvergence.lean`](../../src/CORALean/NN/Layers/PolyFitConvergence.lean)
* [`PolyRangeConvergence.lean`](../../src/CORALean/NN/Layers/PolyRangeConvergence.lean)
* [`PolyRelaxation.lean`](../../src/CORALean/NN/Layers/PolyRelaxation.lean)
* [`PolySampling.lean`](../../src/CORALean/NN/Layers/PolySampling.lean)
* [`SigmoidLinearSigmoid.lean`](../../src/CORALean/NN/Layers/SigmoidLinearSigmoid.lean)
* [`LayerSensitivity.lean`](../../src/CORALean/NN/Operations/LayerSensitivity.lean)
* [`Sensitivity.lean`](../../src/CORALean/NN/Operations/Sensitivity.lean)
