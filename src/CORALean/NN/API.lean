import CORALean.NN.Float.API
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
representation. What a layer asks for is what it calls, and the list is worth
reading: the linear layer — with the convolution, the average pooling and the
batch normalization that *are* it — wants `Mtimes`, `Plus` and a box it can
absorb; an activation layer wants a box it can read off as well, because a
relaxation of ReLU on all of ℝ does not exist; softmax wants only the two boxes,
its slope being zero; and reshape wants `Reindex` alone, which is the one
interface here whose guarantee is an equality. A representation supplying those
runs the whole pipeline, and one that cannot produce a box without linear
programs — `HPolytope`, `VPolytope` — supplies the bounds itself.

Precision is decided in three places and no others: a `Relaxation`, which is all
of `ReLU`, `Sigmoid` and `Tanh`; a pooled window's pivot; and `Softmax`'s box.
Everything else is exact at a representation closed under the operations it
uses, `Reshape` unconditionally so.

Only the layers sit in two arithmetic layers. Everything outside `Layers/` is
already indifferent to the scalar — `Layer` is a structure over any `ContSet`
whose ambient type is `Vec ℝ n`, so the graph and its induction run over a float
representation unchanged, and `Float/` holds the layer constructors alone.
-/
