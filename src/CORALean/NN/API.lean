import CORALean.NN.Layer
import CORALean.NN.Layers.API
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.API
import CORALean.NN.Theorems.API

/-!
# Neural network verification, collected

CORA's `nn`. The pipeline is three things: an input set in whatever
representation the caller likes, a graph of layers each of which encloses the
image of the function it computes, and a specification checked on the result.
`Theorems.Verified` is where those meet.

Written against the `ContSet` interfaces alone, so no layer names a
representation. What a layer asks for is what it calls: the linear layer wants
`Mtimes`, `Plus` and a box it can absorb; an activation layer wants a box it can
read off as well, because a relaxation of ReLU on all of ℝ does not exist. A
representation supplying those runs the whole pipeline, and one that cannot
produce a box without linear programs — `HPolytope`, `VPolytope` — supplies the
bounds itself.

Precision lives entirely in `Layers/Activation`. Everything else is exact at a
representation closed under the two operations it uses, and the enclosure a
network returns is as good as the relaxations its activations chose.
-/
