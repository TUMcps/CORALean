module

public import CORALean.NN.Complexity.API
public import CORALean.NN.Definitions.API
public import CORALean.NN.Graph.API
public import CORALean.NN.Instances
public import CORALean.NN.Layers.API
public import CORALean.NN.NeuralNetwork
public import CORALean.NN.Operations.API
public import CORALean.NN.Theorems.API
public import CORALean.NN.Counterexamples.API

/-!
# Neural network verification, collected

CORA's `nn`. The pipeline is three things: an input set in whatever representation the caller likes,
a graph of layers each of which encloses the image of the function it computes, and a specification
checked on the result. `Theorems.HoldsOfEnclose`/`HoldsAllOfEnclose` is where those meet; `Graph/`
the graph layers. `Definitions/` holds what a network means — the exact chain, the refinable and
reducible forms, the merge buckets, `ReducesAt` — `Operations/` the algorithms that run on them.

Written against the `ContSet` interfaces alone, so no layer names a representation, and what a layer
asks for is what it calls: the linear layer — with the convolution, average pooling and batch
normalization that *are* it — wants `Mtimes`, `Plus` and a box it can absorb; an activation layer a
box it can read off too, a relaxation of ReLU on all of ℝ not existing; softmax only the two boxes;
and reshape `Reindex` alone, whose guarantee is an equality.

Precision is decided in three places: a `Relaxation` (`ReLU`, `Sigmoid`, `Tanh`), a pooled window's
pivot, and `Softmax`'s box; everything else is exact at a representation closed under what it uses.

The layers and the reduction are written once over the scalar and run at ℝ and at a machine
scalar alike; `Layers/Definitions/` holds what they mean over ℝ. `Layer` stores `enclose` and
nothing real, so the graph and its induction run over a float representation unchanged.
`RefinableLayer` and `RefinableNetwork` are that graph with an order per neuron still to choose,
read by `Schedule`.
-/
