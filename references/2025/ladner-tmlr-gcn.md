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
| `Prop. 4` | (§4.2) uncertain message passing needs O(h^3) generators | [`MessagePassingEnclosure.lean`](../../src/CORALean/NN/Graph/MessagePassingEnclosure.lean), [`MessagePassingEnclosureOuter.lean`](../../src/CORALean/NN/Graph/Theorems/MessagePassingEnclosureOuter.lean) |
| `Prop. 5` | (§4.2) GCN layer enclosure with uncertain graph has O(h1 h2^3) generators | [`ConvUncertain.lean`](../../src/CORALean/NN/Graph/ConvUncertain.lean), [`ConvUncertainExact.lean`](../../src/CORALean/NN/Graph/Theorems/ConvUncertainExact.lean) |
| `Lemma 1` | (§3) matrix polynomial zonotope multiplication enclosure, O(h1 h2) generators | [`ConvUncertain.lean`](../../src/CORALean/NN/Graph/ConvUncertain.lean) |
| `Lemma 2` | (§4.2) inverse square root approximation error from critical points incl. endpoints | [`InvSqrt.lean`](../../src/CORALean/NN/Layers/InvSqrt.lean) |
| `Thm. 1` | (§4.2) overall verification complexity is polynomial in uncertain edges and features | — |
| `Sec. 4.3` | Verifying a subgraph rather than the whole graph: a neighbourhood closed under the uncertain edges answers for every node in it. | [`BallLocalityEnumerated.lean`](../../src/CORALean/Examples/BallLocalityEnumerated.lean), [`UncertainGraphLocality.lean`](../../src/CORALean/Examples/UncertainGraphLocality.lean), [`Ball.lean`](../../src/CORALean/NN/Graph/Ball.lean), [`BallEnum.lean`](../../src/CORALean/NN/Graph/BallEnum.lean), [`Mask.lean`](../../src/CORALean/NN/Graph/Mask.lean), [`API.lean`](../../src/CORALean/NN/Graph/Theorems/API.lean), [`AdjAtSupportSubset.lean`](../../src/CORALean/NN/Graph/Theorems/AdjAtSupportSubset.lean), [`AdjAtSymm.lean`](../../src/CORALean/NN/Graph/Theorems/AdjAtSymm.lean), [`DegreeSubmatrixOfBall.lean`](../../src/CORALean/NN/Graph/Theorems/DegreeSubmatrixOfBall.lean), [`DegreeSubmatrixOfBallUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/DegreeSubmatrixOfBallUncertain.lean), [`EdgeMatSymm.lean`](../../src/CORALean/NN/Graph/Theorems/EdgeMatSymm.lean), [`EvalStepsRowBall.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBall.lean), [`EvalStepsRowBallEnum.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBallEnum.lean), [`EvalStepsRowBallOfAdjacency.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBallOfAdjacency.lean), [`EvalStepsRowBallOfAdjacencyUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBallOfAdjacencyUncertain.lean), [`EvalStepsRowMask.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowMask.lean), [`EvalStepsRowMaskUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowMaskUncertain.lean), [`EvalStepsSubmatrix.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsSubmatrix.lean), [`MessagePassingSubmatrixOfBall.lean`](../../src/CORALean/NN/Graph/Theorems/MessagePassingSubmatrixOfBall.lean), [`MessagePassingSubmatrixOfBallUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/MessagePassingSubmatrixOfBallUncertain.lean), [`SubmatrixMulOfClosed.lean`](../../src/CORALean/NN/Graph/Theorems/SubmatrixMulOfClosed.lean), [`UncertainMax.lean`](../../src/CORALean/NN/Graph/UncertainMax.lean) |
| `Cor. 1` | (§4.3) subgraph selection by projection | [`API.lean`](../../src/CORALean/NN/Graph/API.lean), [`Subgraph.lean`](../../src/CORALean/NN/Graph/Subgraph.lean) |
| `Alg. 1` | (§4.2) enclosing the output | — |

## Findings

**Alg. 1 — the output-level labels.** Lines 7 and 9 read `⊳ Graph-level output` and
`⊳ Node-level output`; §2.2 and the paragraph right before Alg. 1 both say the reverse
— a node-level output skips the pooling layer and a graph-level one applies it, and
line 7's branch (`κ=2κ'`) is exactly the one with no pooling layer to apply. CORALean
does not yet formalize Alg. 1, so nothing here reads either label.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`GcnStepsOuter.lean`](../../src/CORALean/NN/Graph/Theorems/GcnStepsOuter.lean)
* [`GcnUncertainOuter.lean`](../../src/CORALean/NN/Graph/Theorems/GcnUncertainOuter.lean)
* [`UncertainAdjExact.lean`](../../src/CORALean/NN/Graph/Theorems/UncertainAdjExact.lean)
* [`UncertainDegreeBounds.lean`](../../src/CORALean/NN/Graph/Theorems/UncertainDegreeBounds.lean)
* [`Uncertain.lean`](../../src/CORALean/NN/Graph/Uncertain.lean)
* [`UncertainDegree.lean`](../../src/CORALean/NN/Graph/UncertainDegree.lean)
