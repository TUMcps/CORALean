import CORALean.NN.Float.API
import CORALean.NN.Graph.API
import CORALean.NN.Layer
import CORALean.NN.Layers.API
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.API
import CORALean.NN.RefinableLayer
import CORALean.NN.RefinableNetwork
import CORALean.NN.Theorems.API

/-!
# Neural network verification, collected

CORA's `nn`. The pipeline is three things: an input set in whatever
representation the caller likes, a graph of layers each of which encloses the
image of the function it computes, and a specification checked on the result.
`Theorems.Verified` is where those meet; `Graph/` is the graph layers, matrix-shaped.

Written against the `ContSet` interfaces alone, so no layer names a
representation, and what a layer asks for is what it calls: the linear layer —
with the convolution, average pooling and batch normalization that *are* it —
wants `Mtimes`, `Plus` and a box it can absorb; an activation layer a box it can
read off too, a relaxation of ReLU on all of ℝ not existing; softmax only the
two boxes; and reshape `Reindex` alone, whose guarantee is an equality.

Precision is decided in three places and no others: a `Relaxation`, which is all
of `ReLU`, `Sigmoid` and `Tanh`; a pooled window's pivot; and `Softmax`'s box.
Everything else is exact at a representation closed under what it uses.

Only the layers sit in two arithmetic layers. Everything outside `Layers/` is already
indifferent to the scalar — `Layer` is a structure over any `ContSet` whose ambient type is
`Vec ℝ n`, so the graph and its induction run over a float representation unchanged, and
`Float/` holds the layer constructors alone. `RefinableLayer` and `RefinableNetwork` are that
graph with an order per neuron still to choose, which `Operations.Schedule` reads and refines.
-/
