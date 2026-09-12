# Formal Verification of Graph Convolutional Networks with Uncertain Node Features and Uncertain Graph Structure

T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional
Networks with Uncertain Node Features and Uncertain Graph Structure". TMLR, 2025.
arXiv:2404.15065.

**Source:** https://arxiv.org/html/2404.15065v2  
**Inventory:** confirmed

Verifying a graph convolutional network when both the node features and the
graph itself are uncertain: the matrix polynomial zonotope, and what a GCN
layer does to one. `NN/Graph/` is this paper.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (§2.2) neural network as iterated layer application | n/a — a preliminary restated from the literature, not a result of this paper |
| `Def. 2` | (§2.2) linear layer | n/a — a preliminary restated from the literature, not a result of this paper |
| `Def. 3` | (§2.2) elementwise activation layer | n/a — a preliminary restated from the literature, not a result of this paper |
| `Def. 4` | (§2.2) graph convolutional layer, degree-normalised adjacency times features times weights | [`Conv.lean`](../../src/CORALean/NN/Graph/Conv.lean) |
| `Def. 5` | (§2.2) global pooling layer, permutation-invariant aggregation | [`Pooling.lean`](../../src/CORALean/NN/Graph/Pooling.lean) |
| `Def. 6` | (§2.3) polynomial zonotope | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Def. 7` | (§3) matrix polynomial zonotope, a 3D generator tensor | [`PolyZonotope.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/PolyZonotope.lean) |
| `Prop. 1` | (§2.4) image enclosure for a nonlinear layer, with bounded generator growth | n/a — restated (Kochdumper et al., 2023, Sec. 3), not a result of this paper; tracked as `Alg. 1` on [Open- and Closed-Loop Neural Network Verification using Polynomial Zonotopes](../2022/kochdumper-arxiv-nn-polyzono.md) |
| `Prop. 2` | (§4.1) GCN layer on uncertain node features is exact | [`Conv.lean`](../../src/CORALean/NN/Graph/Conv.lean), [`ConvExact.lean`](../../src/CORALean/NN/Graph/Theorems/ConvExact.lean), [`ConvExactOfAdjacency.lean`](../../src/CORALean/NN/Graph/Theorems/ConvExactOfAdjacency.lean) |
| `Prop. 3` | (§4.1) sum-pooling layer is exact on matrix polynomial zonotopes | [`Pooling.lean`](../../src/CORALean/NN/Graph/Pooling.lean), [`PoolingExact.lean`](../../src/CORALean/NN/Graph/Theorems/PoolingExact.lean) |
| `Prop. 4` | (§4.2) uncertain message passing needs O(h^3) generators | [`MessagePassingEnclosure.lean`](../../src/CORALean/NN/Graph/MessagePassingEnclosure.lean), [`MessagePassingEnclosureOuter.lean`](../../src/CORALean/NN/Graph/Theorems/MessagePassingEnclosureOuter.lean), [`Complexity/MessagePassingEnclosure.lean`](../../src/CORALean/NN/Graph/Complexity/MessagePassingEnclosure.lean), [`Complexity/MessagePassingEnclosureBigO.lean`](../../src/CORALean/NN/Graph/Complexity/MessagePassingEnclosureBigO.lean) |
| `Prop. 5` | (§4.2) GCN layer enclosure with uncertain graph has O(h1 h2^3) generators | [`ConvUncertain.lean`](../../src/CORALean/NN/Graph/ConvUncertain.lean), [`ConvUncertainExact.lean`](../../src/CORALean/NN/Graph/Theorems/ConvUncertainExact.lean), [`Complexity/ConvUncertain.lean`](../../src/CORALean/NN/Graph/Complexity/ConvUncertain.lean) |
| `Lemma 1` | (§3) matrix polynomial zonotope multiplication enclosure, O(h1 h2) generators | [`ConvUncertain.lean`](../../src/CORALean/NN/Graph/ConvUncertain.lean) |
| `Lemma 2` | (§4.2) inverse square root approximation error from critical points incl. endpoints | [`InvSqrt.lean`](../../src/CORALean/NN/Layers/InvSqrt.lean) |
| `Thm. 1` | (§4.2) overall verification complexity is polynomial in uncertain edges and features | [`Complexity/API.lean`](../../src/CORALean/NN/Graph/Complexity/API.lean), [`Complexity/Conv.lean`](../../src/CORALean/NN/Graph/Complexity/Conv.lean), [`Complexity/ConvUncertain.lean`](../../src/CORALean/NN/Graph/Complexity/ConvUncertain.lean), [`Complexity/GcnSteps.lean`](../../src/CORALean/NN/Graph/Complexity/GcnSteps.lean), [`Complexity/GcnStepsBigO.lean`](../../src/CORALean/NN/Graph/Complexity/GcnStepsBigO.lean), [`Complexity/MessagePassingEnclosure.lean`](../../src/CORALean/NN/Graph/Complexity/MessagePassingEnclosure.lean), [`Complexity/MessagePassingEnclosureBigO.lean`](../../src/CORALean/NN/Graph/Complexity/MessagePassingEnclosureBigO.lean), [`Complexity/Pooling.lean`](../../src/CORALean/NN/Graph/Complexity/Pooling.lean); the graph operations' counts and their composition over κ' message-passing steps, which is the `h_e^(3κ')` the claim rests on — the `c_max` and `n_max` terms the bound adds are the one generator per neuron of `Prop. 1`, tracked on that row's own page |
| `Sec. 4.3` | Verifying a subgraph rather than the whole graph: a neighbourhood closed under the uncertain edges answers for every node in it. | [`BallLocalityEnumerated.lean`](../../src/CORALean/Examples/BallLocalityEnumerated.lean), [`UncertainGraphLocality.lean`](../../src/CORALean/Examples/UncertainGraphLocality.lean), [`Ball.lean`](../../src/CORALean/NN/Graph/Ball.lean), [`BallEnum.lean`](../../src/CORALean/NN/Graph/BallEnum.lean), [`Mask.lean`](../../src/CORALean/NN/Graph/Mask.lean), [`API.lean`](../../src/CORALean/NN/Graph/Theorems/API.lean), [`AdjAtSupportSubset.lean`](../../src/CORALean/NN/Graph/Theorems/AdjAtSupportSubset.lean), [`AdjAtSymm.lean`](../../src/CORALean/NN/Graph/Theorems/AdjAtSymm.lean), [`DegreeSubmatrixOfBall.lean`](../../src/CORALean/NN/Graph/Theorems/DegreeSubmatrixOfBall.lean), [`DegreeSubmatrixOfBallUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/DegreeSubmatrixOfBallUncertain.lean), [`EdgeMatSymm.lean`](../../src/CORALean/NN/Graph/Theorems/EdgeMatSymm.lean), [`EvalStepsRowBall.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBall.lean), [`EvalStepsRowBallEnum.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBallEnum.lean), [`EvalStepsRowBallOfAdjacency.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBallOfAdjacency.lean), [`EvalStepsRowBallOfAdjacencyUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBallOfAdjacencyUncertain.lean), [`EvalStepsRowMask.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowMask.lean), [`EvalStepsRowMaskUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowMaskUncertain.lean), [`EvalStepsSubmatrix.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsSubmatrix.lean), [`MessagePassingSubmatrixOfBall.lean`](../../src/CORALean/NN/Graph/Theorems/MessagePassingSubmatrixOfBall.lean), [`MessagePassingSubmatrixOfBallUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/MessagePassingSubmatrixOfBallUncertain.lean), [`SubmatrixMulOfClosed.lean`](../../src/CORALean/NN/Graph/Theorems/SubmatrixMulOfClosed.lean), [`UncertainMax.lean`](../../src/CORALean/NN/Graph/UncertainMax.lean) |
| `Cor. 1` | (§4.3) subgraph selection by projection | [`API.lean`](../../src/CORALean/NN/Graph/API.lean), [`Subgraph.lean`](../../src/CORALean/NN/Graph/Subgraph.lean) |
| `Alg. 1` | (§4.2) enclosing the output: the message passing once, then κ' convolution/activation pairs, then either return or pool and finish with standard layers | n/a — a demonstration pipeline, and printed as one: §4.2 assembles it "to demonstrate the polynomial time complexity" at the single architecture of Fig. 2, and every line delegates to a numbered result that already has a row here — `Prop. 4` (line 3), `Prop. 5` (5), `Prop. 1` (6 and 14), `Prop. 3` (11), `Def. 2` (13). No step is Alg. 1's own, and the guarantee `𝒴 ⊇ 𝒴*` it returns is not claimed here either: it is the first sentence of `Thm. 1`. The concatenation is what CORALean builds — [`GcnStepsOuter.lean`](../../src/CORALean/NN/Graph/Theorems/GcnStepsOuter.lean) is the convolutions of lines 4–7 at one uncertain graph, [`PoolingExact.lean`](../../src/CORALean/NN/Graph/Theorems/PoolingExact.lean) is line 11, and `NeuralNetwork.enclose` the tail from line 12; the activation layers of lines 6 and 14 are `Prop. 1`'s, and that row names the paper they belong to |

## Findings

**Alg. 1 — the output-level labels.** Lines 8 and 10 read `⊳ Graph-level output` and
`⊳ Node-level output`; §2.2 and the paragraph right before Alg. 1 both say the reverse
— a node-level output skips the pooling layer and a graph-level one applies it, and
line 8's branch (`κ=2κ'`) is exactly the one with no pooling layer to apply. Nothing in
CORALean reads either label: the row above marks Alg. 1 `n/a`.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`GcnStepsOuter.lean`](../../src/CORALean/NN/Graph/Theorems/GcnStepsOuter.lean)
* [`GcnUncertainOuter.lean`](../../src/CORALean/NN/Graph/Theorems/GcnUncertainOuter.lean)
* [`UncertainAdjExact.lean`](../../src/CORALean/NN/Graph/Theorems/UncertainAdjExact.lean)
* [`UncertainDegreeBounds.lean`](../../src/CORALean/NN/Graph/Theorems/UncertainDegreeBounds.lean)
* [`Uncertain.lean`](../../src/CORALean/NN/Graph/Uncertain.lean)
* [`UncertainDegree.lean`](../../src/CORALean/NN/Graph/UncertainDegree.lean)
