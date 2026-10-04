import CORALean.NN.Graph.Operations.AdjAt
import CORALean.NN.Graph.Operations.AdjMax
import CORALean.NN.Graph.Operations.Ball
import CORALean.NN.Graph.Operations.BallEnum
import CORALean.NN.Graph.Operations.Degree
import CORALean.NN.Graph.Operations.DegreeAt
import CORALean.NN.Graph.Operations.DegreeCoeff
import CORALean.NN.Graph.Operations.DegreeInf
import CORALean.NN.Graph.Operations.DegreeSup
import CORALean.NN.Graph.Operations.EdgeDegree
import CORALean.NN.Graph.Operations.EdgeMat
import CORALean.NN.Graph.Operations.EvalSteps
import CORALean.NN.Graph.Operations.Gcn
import CORALean.NN.Graph.Operations.GcnLin
import CORALean.NN.Graph.Operations.GcnShared
import CORALean.NN.Graph.Operations.GcnSteps
import CORALean.NN.Graph.Operations.GcnUncertain
import CORALean.NN.Graph.Operations.Linear
import CORALean.NN.Graph.Operations.LinearBias
import CORALean.NN.Graph.Operations.LinearLin
import CORALean.NN.Graph.Operations.LinearPolyZonotope
import CORALean.NN.Graph.Operations.Mask
import CORALean.NN.Graph.Operations.MatMulBilin
import CORALean.NN.Graph.Operations.MessagePassing
import CORALean.NN.Graph.Operations.MessagePassingEnclosure
import CORALean.NN.Graph.Operations.OnesRow
import CORALean.NN.Graph.Operations.Select
import CORALean.NN.Graph.Operations.SelectMat
import CORALean.NN.Graph.Operations.SqrtBroadcast
import CORALean.NN.Graph.Operations.SqrtCol
import CORALean.NN.Graph.Operations.SqrtConst
import CORALean.NN.Graph.Operations.SqrtEdgeCoeff
import CORALean.NN.Graph.Operations.SqrtError
import CORALean.NN.Graph.Operations.SqrtOffset
import CORALean.NN.Graph.Operations.SqrtRow
import CORALean.NN.Graph.Operations.SqrtSlope
import CORALean.NN.Graph.Operations.SumPool
import CORALean.NN.Graph.Operations.SumPoolLin
import CORALean.NN.Graph.Operations.UncertainAdj
import CORALean.NN.Graph.Operations.UncertainAdjPad

/-!
# What the graph layers compute, collected

`ball`/`ballEnum` are `[1, §4.3]`'s locality neighbourhood, enumerated; `mask` zeroes a matrix
outside a node set. `degree`/`messagePassing` build `P` at a known graph, `gcnLin`/`gcn` the layer
itself, `sumPoolLin`/`sumPool` the pooling layer, `select` the subgraph projection.

`edgeMat`/`adjAt`/`adjMax` are an uncertain graph's adjacency at one, every, and the heaviest
admissible edge weighting; `uncertainAdj`/`uncertainAdjPad` are its exact and self-looped matrix
polynomial zonotopes. `matMulBilin`/`gcnShared`/`gcnUncertain`/`evalSteps`/`gcnSteps` are the
uncertain convolution and its chain over steps, [1, Prop. 5].

`degreeAt`/`degreeInf`/`degreeSup`/`edgeDegree`/`degreeCoeff` bracket an uncertain degree;
`sqrtSlope`/`sqrtOffset`/`sqrtError`/`sqrtConst`/`sqrtEdgeCoeff` are the inverse-square-root
relaxation read over that bracket, `sqrtBroadcast`/`sqrtRow`/`sqrtCol` broadcasting it into the
two normalising matrices `messagePassingEnclosure`, [1, Prop. 4], pairs entrywise with the padded
adjacency.

All ℝ-only, `noncomputable` where a search or an inverse square root has no computable form yet —
see `scripts/noncomputable-allowlist.txt`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/
