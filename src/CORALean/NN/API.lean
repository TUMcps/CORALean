import CORALean.NN.BucketTolerance
import CORALean.NN.Chain
import CORALean.NN.CompressionPreprocessing
import CORALean.NN.Float.API
import CORALean.NN.Graph.API
import CORALean.NN.Layer
import CORALean.NN.Layers.API
import CORALean.NN.MergeBucket
import CORALean.NN.MinimalAbstractExplanationSearch
import CORALean.NN.MinimalExplanationSearch
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.API
import CORALean.NN.ReduceOnTheFly
import CORALean.NN.ReducibleNetwork
import CORALean.NN.Reduction
import CORALean.NN.RefinableLayer
import CORALean.NN.RefinableNetwork
import CORALean.NN.Schedule
import CORALean.NN.Theorems.API

/-!
# Neural network verification, collected

CORA's `nn`. The pipeline is three things: an input set in whatever
representation the caller likes, a graph of layers each of which encloses the
image of the function it computes, and a specification checked on the result.
`Theorems.HoldsOfEnclose`/`HoldsAllOfEnclose` is where those meet; `Graph/` the graph layers.
`MergeBucket` cuts a nonlinear layer's neurons, `Reduction`'s `ReducesAt` reduces many soundly,
and `BucketTolerance`, `ReduceOnTheFly`, `CompressionPreprocessing` choose where to.

Written against the `ContSet` interfaces alone, so no layer names a
representation, and what a layer asks for is what it calls: the linear layer —
with the convolution, average pooling and batch normalization that *are* it —
wants `Mtimes`, `Plus` and a box it can absorb; an activation layer a box it can
read off too, a relaxation of ReLU on all of ℝ not existing; softmax only the
two boxes; and reshape `Reindex` alone, whose guarantee is an equality.

Precision is decided in three places: a `Relaxation` (`ReLU`, `Sigmoid`, `Tanh`), a pooled window's
pivot, and `Softmax`'s box; everything else is exact at a representation closed under what it uses.

Only what reads weights sits in an arithmetic layer's namespace — the layers, and the reduction
over a `ReducibleNetwork`; the rest sits in `CORALean`. `Layer` stores `enclose` and nothing
real, so the graph and its induction run over a float representation unchanged. `RefinableLayer`
and `RefinableNetwork` are that graph with an order per neuron still to choose, read by `Schedule`.
-/
