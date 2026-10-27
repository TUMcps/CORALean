module

public import CORALean.NN.Graph.Operations.AdjAt
public import CORALean.NN.Graph.Operations.AdjMax
public import CORALean.NN.Graph.Operations.Ball
public import CORALean.NN.Graph.Operations.BallEnum
public import CORALean.NN.Graph.Operations.Degree
public import CORALean.NN.Graph.Operations.DegreeAt
public import CORALean.NN.Graph.Operations.DegreeCoeff
public import CORALean.NN.Graph.Operations.DegreeSup
public import CORALean.NN.Graph.Operations.EdgeDegree
public import CORALean.NN.Graph.Operations.EdgeMat
public import CORALean.NN.Graph.Operations.EvalSteps
public import CORALean.NN.Graph.Operations.Gcn
public import CORALean.NN.Graph.Operations.GcnLin
public import CORALean.NN.Graph.Operations.GcnShared
public import CORALean.NN.Graph.Operations.GcnSteps
public import CORALean.NN.Graph.Operations.GcnUncertain
public import CORALean.NN.Graph.Operations.Linear
public import CORALean.NN.Graph.Operations.Basic
public import CORALean.NN.Graph.Operations.LinearLin
public import CORALean.NN.Graph.Operations.LinearPolyZonotope
public import CORALean.NN.Graph.Operations.Mask
public import CORALean.NN.Graph.Operations.MatMulBilin
public import CORALean.NN.Graph.Operations.MessagePassing
public import CORALean.NN.Graph.Operations.MessagePassingEnclosure
public import CORALean.NN.Graph.Operations.OnesRow
public import CORALean.NN.Graph.Operations.ReduceGNNForNode
public import CORALean.NN.Graph.Operations.ReduceKeep
public import CORALean.NN.Graph.Operations.ReducedSteps
public import CORALean.NN.Graph.Operations.Select
public import CORALean.NN.Graph.Operations.SelectMat
public import CORALean.NN.Graph.Operations.SqrtConst
public import CORALean.NN.Graph.Operations.SqrtEdgeCoeff
public import CORALean.NN.Graph.Operations.SqrtOffset
public import CORALean.NN.Graph.Operations.SqrtSlope
public import CORALean.NN.Graph.Operations.SumPool
public import CORALean.NN.Graph.Operations.SumPoolLin
public import CORALean.NN.Graph.Operations.UncertainAdj
public import CORALean.NN.Graph.Operations.EvalStepsLayers
public import CORALean.NN.Graph.Operations.Bfs
public import CORALean.NN.Graph.Operations.EvalLayers
public import CORALean.NN.Graph.Operations.GcnActSteps
public import CORALean.NN.Graph.Operations.TailEval
public import CORALean.NN.Graph.Operations.TailEnclose
public import CORALean.NN.Graph.Operations.Alg1Node
public import CORALean.NN.Graph.Operations.Alg1Graph
public import CORALean.NN.Graph.Operations.Flatten
public import CORALean.NN.Graph.Operations.FloatBiasPoint
public import CORALean.NN.Graph.Operations.FloatGcn
public import CORALean.NN.Graph.Operations.FloatLinear
public import CORALean.NN.Graph.Operations.FloatRightMat
public import CORALean.NN.Graph.Operations.FloatSumPool
public import CORALean.NN.Graph.Operations.SupportFloat
public import CORALean.NN.Graph.Operations.BallFloat
public import CORALean.NN.Graph.Operations.ReduceKeepFloat
public import CORALean.NN.Graph.Operations.ReducedStepsFloat
public import CORALean.NN.Graph.Operations.ReduceGNNForNodeFloat

/-!
# What the graph layers compute, collected

`ball`/`ballEnum` are `[1, §4.3]`'s locality neighbourhood, enumerated; `mask` zeroes a matrix
outside a node set. `degree`/`messagePassing` build `P` at a known graph, `gcnLin`/`gcn` the layer
itself, `sumPoolLin`/`sumPool` the pooling layer, `select` the subgraph projection.

`edgeMat`/`adjAt`/`adjMax` are an uncertain graph's adjacency at one, every, and the heaviest
admissible edge weighting; `uncertainAdj`/`aux_uncertainAdjPad` are its exact and self-looped matrix
polynomial zonotopes. `matMulBilin`/`gcnShared`/`gcnUncertain`/`evalSteps`/`gcnSteps` are the
uncertain convolution and its chain over steps, [1, Prop. 5].

`degreeAt`/`degreeSup`/`edgeDegree`/`degreeCoeff` bracket an uncertain degree;
`sqrtSlope`/`sqrtOffset`/`aux_sqrtError`/`sqrtConst`/`sqrtEdgeCoeff` are the inverse-square-root
relaxation read over that bracket, `aux_sqrtBroadcast`/`aux_sqrtRow`/`aux_sqrtCol` broadcasting it
into the two normalising matrices `messagePassingEnclosure`, [1, Prop. 4], pairs entrywise with the
padded adjacency.

All ℝ-only, `noncomputable` where a search or an inverse square root has no computable form yet,
and says so in its docstring.

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/
