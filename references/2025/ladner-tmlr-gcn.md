# Formal Verification of Graph Convolutional Networks with Uncertain Node Features and Uncertain Graph Structure

```bibtex
@article{ladner2025formal,
  author = {Ladner, T. and Eichelbeck, M. and Althoff, M.},
  title = {Formal Verification of Graph Convolutional Networks with Uncertain Node Features and Uncertain Graph Structure},
  journal = {Transactions on Machine Learning Research},
  year = {2025}
}
```

**Source:** https://arxiv.org/html/2404.15065v2  
**Inventory:** confirmed

Verifying a graph convolutional network when both the node features and the
graph itself are uncertain: the matrix polynomial zonotope, and what a GCN
layer does to one. `NN/Graph/` is this paper.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (§2.2) neural network as iterated layer application | n/a — a preliminary restated from the literature, not a result of this paper | `restated` |
| `Def. 2` | (§2.2) linear layer | n/a — a preliminary restated from the literature, not a result of this paper | `restated` |
| `Def. 3` | (§2.2) elementwise activation layer | n/a — a preliminary restated from the literature, not a result of this paper | `restated` |
| `Def. 4` | (§2.2) graph convolutional layer, degree-normalised adjacency times features times weights | [`Gcn.lean`](../../src/CORALean/NN/Graph/Operations/Gcn.lean) | `correct` |
| `Def. 5` | (§2.2) global pooling layer, any permutation-invariant aggregation ψ | [`IsPermInvariant.lean`](../../src/CORALean/NN/Graph/Definitions/IsPermInvariant.lean) — the layer is any aggregation `ψ` over the nodes that a permutation of the rows leaves unchanged; [`SumPoolLin.lean`](../../src/CORALean/NN/Graph/Operations/SumPoolLin.lean), [`SumPoolLinPermInvariant.lean`](../../src/CORALean/NN/Graph/Theorems/SumPoolLinPermInvariant.lean) — Eq. (1)'s sum, such a `ψ`, and the one `Prop. 3`'s exactness is about | `correct` |
| `Def. 6` | (§2.3) polynomial zonotope | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) | `restated` |
| `Def. 7` | (§3) matrix polynomial zonotope, a 3D generator tensor | [`PolyZonotope.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/PolyZonotope.lean) | `correct` |
| `Prop. 1` | (§2.4) image enclosure for a nonlinear layer, with bounded generator growth | n/a — restated (Kochdumper et al., 2023, Sec. 3), not a result of this paper; tracked as `Alg. 1` on [Open- and Closed-Loop Neural Network Verification using Polynomial Zonotopes](../2022/kochdumper-arxiv-nn-polyzono.md) | `restated` |
| `Prop. 2` | (§4.1) GCN layer on uncertain node features is exact | [`Gcn.lean`](../../src/CORALean/NN/Graph/Operations/Gcn.lean), [`ConvExact.lean`](../../src/CORALean/NN/Graph/Theorems/ConvExact.lean), [`ConvExactOfAdjacency.lean`](../../src/CORALean/NN/Graph/Theorems/ConvExactOfAdjacency.lean) | `correct` |
| `Prop. 3` | (§4.1) sum-pooling layer is exact on matrix polynomial zonotopes | [`SumPool.lean`](../../src/CORALean/NN/Graph/Operations/SumPool.lean), [`PoolingExact.lean`](../../src/CORALean/NN/Graph/Theorems/PoolingExact.lean) | `correct` |
| `Prop. 4` | (§4.2) uncertain message passing needs O(h^3) generators | [`MessagePassingEnclosure.lean`](../../src/CORALean/NN/Graph/Operations/MessagePassingEnclosure.lean), [`MessagePassingEnclosureOuter.lean`](../../src/CORALean/NN/Graph/Theorems/MessagePassingEnclosureOuter.lean), [`MessagePassingEnclosureP.lean`](../../src/CORALean/NN/Graph/Complexity/Space/Theorems/MessagePassingEnclosureP.lean), [`MessagePassingEnclosureHIsBigO.lean`](../../src/CORALean/NN/Graph/Complexity/Space/Theorems/MessagePassingEnclosureHIsBigO.lean) | `correct` |
| `Prop. 5` | (§4.2) GCN layer enclosure with uncertain graph has O(h1 h2^3) generators | [`GcnUncertain.lean`](../../src/CORALean/NN/Graph/Operations/GcnUncertain.lean), [`GcnUncertainOuter.lean`](../../src/CORALean/NN/Graph/Theorems/GcnUncertainOuter.lean) — `gcn_mem_gcnUncertain`, the enclosure the proposition claims: at admissible edge weights and any point of the feature set, the graph's own `P H W` lies in the computed set. [`ConvUncertainExact.lean`](../../src/CORALean/NN/Graph/Theorems/ConvUncertainExact.lean) is the narrower `gcnUncertain_exact` (the padded product's factor image *is* its `construct`), and [`GcnSharedH.lean`](../../src/CORALean/NN/Graph/Complexity/Space/Theorems/GcnSharedH.lean),  the count | `correct` |
| `Lemma 1` | (§3) matrix polynomial zonotope multiplication enclosure, O(h1 h2) generators | [`MatMulBilin.lean`](../../src/CORALean/NN/Graph/Operations/MatMulBilin.lean), [`GcnSharedP.lean`](../../src/CORALean/NN/Graph/Theorems/GcnSharedP.lean) — the bilinear map `gcnShared` is `bilin` at, the product at a common identifier vector. What the lemma asserts is proved beside it and is not linked from this row, neither file naming this paper: `PolyZonotope.bilin_exact` in `ContSet/PolyZonotope/Real/Theorems/BilinExact.lean` and `GNN.gcnShared_exact` in `NN/Graph/Theorems/GcnSharedExact.lean`, with the count `gcnShared_h = (P.h+1)·(H.h+1)` in `NN/Graph/Complexity/Space/ConvUncertain.lean` | `correct` |
| `Lemma 2` | (§4.2) inverse square root approximation error, the **maximum** of `\|f − p\|` over the critical points and the endpoints | [`InvSqrt.lean`](../../src/CORALean/NN/Layers/Definitions/InvSqrt.lean), [`InvSqrtRelaxation.lean`](../../src/CORALean/NN/Layers/Definitions/InvSqrtRelaxation.lean), [`InvSqrtRelaxationEncloses.lean`](../../src/CORALean/NN/Layers/Theorems/Real/InvSqrtRelaxationEncloses.lean) — a sound *bound*, not that maximum, and the departure [the coverage README, departures from CORA](../coverage/README.md#departures-from-cora-that-belong-to-no-single-method) records: `invSqrt x = (√(max x 1))⁻¹` is clamped at the degree bound `1`, and its error comes from `Relaxation.ofAntitone`'s range bound and a mean-value bracket (`invSqrtRelaxationDeriv`, guarded by `1 ≤ l`), combined by `tighter`. Nothing evaluates `\|f − p\|` at `{l, ∛((1/2a)²), u}` | `correct` |
| `Thm. 1` | (§4.2) Given a neural network Φ with κ layers and κ' message passing steps, an uncertain graph G = (N, E) with \|N\| nodes and h_e uncertain edges, and an uncertain input X with h_x generators, Alg. 1 satisfies the problem statement in Sec. 2.5. | [`Alg1NodeSound.lean`](../../src/CORALean/NN/Graph/Theorems/Alg1NodeSound.lean), [`Alg1GraphSound.lean`](../../src/CORALean/NN/Graph/Theorems/Alg1GraphSound.lean), [`EvalLayersMemGcnActStepsUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/EvalLayersMemGcnActStepsUncertain.lean), [`EvalLayersMemGcnActSteps.lean`](../../src/CORALean/NN/Graph/Theorems/EvalLayersMemGcnActSteps.lean), [`TailEncloseMem.lean`](../../src/CORALean/NN/Graph/Theorems/TailEncloseMem.lean) — `GNN.alg1Node_isSound` and `GNN.alg1Graph_isSound`: for every weighting `lam ∈ [0, 1]` of the uncertain edges (the subsets `E ⊆ ~E` are `lam ∈ {0, 1}`) and every input of `X`, the network the graph runs, with its activations, lies in the set `Alg. 1` returns, node-level and graph-level (the sum pooling and the standard layers after it). The activation enclosure is a hypothesis, `ActLayer.Encloses`, the dependency-keeping form of `Prop. 1` | `underspecified` — `Prop. 1` is printed as an outer approximation, and `Alg. 1` reuses one `P` at every step, which needs each activation enclosure to keep the factors of its input and give its new generators factors of their own; see Findings |
| `Thm. 1 (generators)` | The number of generators of the computed output enclosure Y is h_y ∈ O(h_e^{3κ'} (h_x + \|N\| c_max) + (κ − 2κ') n_max), with c_max := max over k' ∈ [κ'] of c_{2k'} the most features within the graph layers and n_max := max over k ∈ {2κ'+2, …, κ} of n_k the most output neurons of the non-graph-based layers after the pooling. | [`Alg1GraphIsBigO.lean`](../../src/CORALean/NN/Graph/Complexity/Space/Theorems/Alg1GraphIsBigO.lean), [`Alg1GraphCountLe.lean`](../../src/CORALean/NN/Graph/Complexity/Space/Theorems/Alg1GraphCountLe.lean), [`Alg1NodeEqGcnActSteps.lean`](../../src/CORALean/NN/Graph/Complexity/Space/Theorems/Alg1NodeEqGcnActSteps.lean), [`Alg1NodeHLe.lean`](../../src/CORALean/NN/Graph/Complexity/Space/Theorems/Alg1NodeHLe.lean), [`GcnActStepsHLe.lean`](../../src/CORALean/NN/Graph/Complexity/Space/Theorems/GcnActStepsHLe.lean), [`TailEncloseCountLe.lean`](../../src/CORALean/NN/Graph/Complexity/Space/Theorems/TailEncloseCountLe.lean) — `GNN.alg1Graph_isBigO`: with the number of uncertain edges and `h_x` both growing, `h_y = O(m^(3κ') (h_x + \|N\| c_max) + E)`, `E` what the standard layers after the pooling add; assembled from `messagePassingEnclosure_h_le` (`O(m³)`), `gcnShared_h` (`(P.h+1)(h+1)`), the activation's at most `\|N\| c` more generators (`ActLayer.AddsAtMost`, `Prop. 1`), the pooling and linear layers leaving the count alone and `tailEnclose_count_le` for the layers after it. The paper's `(κ − 2κ') n_max` bounds `E` | `correct` |
| `Sec. 4.3` | Verifying a subgraph rather than the whole graph: a neighbourhood closed under the uncertain edges answers for every node in it. | [`Ball.lean`](../../src/CORALean/NN/Graph/Operations/Ball.lean), [`Bfs.lean`](../../src/CORALean/NN/Graph/Operations/Bfs.lean), [`BfsVisitedEqBall.lean`](../../src/CORALean/NN/Graph/Theorems/BfsVisitedEqBall.lean), [`AdjMax.lean`](../../src/CORALean/NN/Graph/Operations/AdjMax.lean), [`SubmatrixMulOfClosed.lean`](../../src/CORALean/NN/Graph/Theorems/SubmatrixMulOfClosed.lean), [`EvalStepsLayers.lean`](../../src/CORALean/NN/Graph/Operations/EvalStepsLayers.lean), [`EvalStepsLayersRowMask.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsLayersRowMask.lean), [`EvalStepsLayersSubmatrix.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsLayersSubmatrix.lean), [`EvalStepsLayersRowBall.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsLayersRowBall.lean), [`EvalStepsLayersRowBallEnum.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsLayersRowBallEnum.lean), [`EvalStepsLayersRowBallOfAdjacencyUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsLayersRowBallOfAdjacencyUncertain.lean), [`EvalStepsLayersRowBfsUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsLayersRowBfsUncertain.lean), [`EvalStepsRowBall.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBall.lean), [`EvalStepsRowMaskUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowMaskUncertain.lean), [`EvalStepsRowBallOfAdjacencyUncertain.lean`](../../src/CORALean/NN/Graph/Theorems/EvalStepsRowBallOfAdjacencyUncertain.lean), [`ReducedSteps.lean`](../../src/CORALean/NN/Graph/Operations/ReducedSteps.lean), [`ReduceKeep.lean`](../../src/CORALean/NN/Graph/Operations/ReduceKeep.lean), [`ReduceGNNForNode.lean`](../../src/CORALean/NN/Graph/Operations/ReduceGNNForNode.lean), [`ReduceGNNForNodeExact.lean`](../../src/CORALean/NN/Graph/Theorems/ReduceGNNForNodeExact.lean) — `GNN.bfs_visited`: the breadth-first search from the node, expanding the frontier along every uncertain edge, finds `GNN.ball`. See the Findings. | `correct` |
| `Cor. 1` | (§4.3) subgraph selection by projection | [`API.lean`](../../src/CORALean/NN/Graph/API.lean), [`Select.lean`](../../src/CORALean/NN/Graph/Operations/Select.lean), [`SelectMul.lean`](../../src/CORALean/NN/Graph/Theorems/SelectMul.lean) | `correct` |
| `Alg. 1` | (§4.2) enclosing the output: the message passing once, then κ' convolution/activation pairs, then either return or pool and finish with standard layers | [`Alg1Node.lean`](../../src/CORALean/NN/Graph/Operations/Alg1Node.lean), [`Alg1Graph.lean`](../../src/CORALean/NN/Graph/Operations/Alg1Graph.lean), [`GcnActSteps.lean`](../../src/CORALean/NN/Graph/Operations/GcnActSteps.lean), [`TailEnclose.lean`](../../src/CORALean/NN/Graph/Operations/TailEnclose.lean), [`TailEval.lean`](../../src/CORALean/NN/Graph/Operations/TailEval.lean), [`EvalLayers.lean`](../../src/CORALean/NN/Graph/Operations/EvalLayers.lean) — `alg1Node` (lines 1-6 and 8) and `alg1Graph` (lines 1-6 and 10-14), one named `let` per line: the input made dependent (line 1), `messagePassingEnclosure` (line 2, `Prop. 4`), `gcnActSteps` (lines 3-6: `gcnShared`, `Prop. 5`, then the activation enclosure, `Prop. 1`, with `P` padded by the factors that adds), `sumPool` (line 10, `Prop. 3`) and `tailEnclose` (lines 11-14). The exact network it encloses is `evalLayers` and `tailEval` | `underspecified` — the output-level labels of lines 8 and 10 are swapped, the loops of lines 3 and 11 do not say they step by two and the last pass of line 11 applies an activation past layer κ, and the input's independent generators are made dependent, as `Lemma 1` needs; see Findings |
| `Prop. 6` | (Appendix, Quadratic Map, Kochdumper 2022, Prop. 3.1.30) quadMap(PZ₁,PZ₂,Q) of two polynomial zonotopes with a common identifier vector, Eq. (15) | n/a — restated; the row's own attribution is the paper's. Tracked as `Prop. 13` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) | `restated` |

## Findings

**Alg. 1 — the output-level labels.** Lines 8 and 10 read `⊳ Graph-level output` and
`⊳ Node-level output`; §2.2 and the paragraph right before Alg. 1 both say the reverse
— a node-level output skips the pooling layer and a graph-level one applies it, and
line 8's branch (`κ=2κ'`) is exactly the one with no pooling layer to apply. Nothing in
CORALean reads either label: the row above marks Alg. 1 `n/a`.

**Thm. 1 and Alg. 1 — what the algorithm leaves open.** The convolution of a step is `P ⊡ H` of
`Lemma 1`, which asks the two sets for a common identifier vector and has no independent generators,
and `Alg. 1` reuses the one `P` of line 2 at every step so that an edge is the same factor
throughout. For that, the enclosure of an activation (`Prop. 1`, "outer-approximative output set
with at most n_k more generators") has to keep the identifiers of its input and give the generators
it adds identifiers of their own, which `Prop. 1` does not say. The independent generators of the
input `X` and of each enclosure have to be made dependent before the next convolution.
`ActLayer.Encloses` is the first requirement, `PolyZonotope.dependent` the second. The loop of line
3 (`k' = 2, …, 2κ'`) runs a pair of layers per pass and so steps by two, and the loop of line 11
(`k = 2κ' + 2, 2κ' + 4, …, κ`) applies an activation `k + 1` at its last pass, past the last layer
κ; read with the bound κ - 1. None of this changes the count of `Thm. 1`.
[`ActLayer.lean`](../../src/CORALean/NN/Graph/Definitions/ActLayer.lean),
[`Alg1Node.lean`](../../src/CORALean/NN/Graph/Operations/Alg1Node.lean)

**`Sec. 4.3` — the reduction of node-level outputs.** `GNN.evalStepsLayers_row_bfs_uncertain`: for
the network of `L` message-passing steps with a per-node layer after each (a convolution's
activation, and any further node-level layers), a node's output row at every admissible weighting of
the uncertain edges is the same row of the network run on the subgraph that search finds, `(L + 1)`
hops out. Message passing is computed from that subgraph's own adjacency (the extra hop is the
degrees of both endpoints). The layer-free chain is `evalSteps_row_ball_of_adjacency_uncertain`, and
`reduceGNNForNode_exact` is CORA's shrinking-node-set form of it. A graph-level output ends in a
pooling over every node, which no ball reduces. The paper reduces node-level outputs.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`AdjAt.lean`](../../src/CORALean/NN/Graph/Operations/AdjAt.lean)
* [`Degree.lean`](../../src/CORALean/NN/Graph/Operations/Degree.lean)
* [`DegreeAt.lean`](../../src/CORALean/NN/Graph/Operations/DegreeAt.lean)
* [`EdgeMat.lean`](../../src/CORALean/NN/Graph/Operations/EdgeMat.lean)
* [`GcnStepsOuter.lean`](../../src/CORALean/NN/Graph/Theorems/GcnStepsOuter.lean)
* [`InvSqrtEqRpow.lean`](../../src/CORALean/NN/Layers/Theorems/Real/InvSqrtEqRpow.lean)
* [`OnesRow.lean`](../../src/CORALean/NN/Graph/Operations/OnesRow.lean)
* [`SumPoolLinApply.lean`](../../src/CORALean/NN/Graph/Theorems/SumPoolLinApply.lean)
* [`UncertainAdj.lean`](../../src/CORALean/NN/Graph/Operations/UncertainAdj.lean)
* [`UncertainAdjExact.lean`](../../src/CORALean/NN/Graph/Theorems/UncertainAdjExact.lean)
* [`UncertainDegreeBounds.lean`](../../src/CORALean/NN/Graph/Theorems/UncertainDegreeBounds.lean)
