import CORALean.NN.Layers.Definitions.ActivationLayer
import CORALean.NN.Layers.Definitions.ActivationPoly
import CORALean.NN.Layers.Definitions.ActivationPolyExactLayer
import CORALean.NN.Layers.Definitions.ActivationPolyLayer
import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
import CORALean.NN.Layers.Definitions.AvgPoolLayer
import CORALean.NN.Layers.Definitions.BatchNorm
import CORALean.NN.Layers.Definitions.BatchNormLayer
import CORALean.NN.Layers.Definitions.ConvLayer
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.EvalPoly
import CORALean.NN.Layers.Definitions.IdentityLayer
import CORALean.NN.Layers.Definitions.InvSqrt
import CORALean.NN.Layers.Definitions.InvSqrtRelaxation
import CORALean.NN.Layers.Definitions.LeakyRelu
import CORALean.NN.Layers.Definitions.LinearLayer
import CORALean.NN.Layers.Definitions.LinearWithErrorLayer
import CORALean.NN.Layers.Definitions.MaxPoolLayer
import CORALean.NN.Layers.Definitions.PolyAffineConj
import CORALean.NN.Layers.Definitions.PolyDerivBound
import CORALean.NN.Layers.Definitions.PolyFamily
import CORALean.NN.Layers.Definitions.PolyFit
import CORALean.NN.Layers.Definitions.PolyOfSampling
import CORALean.NN.Layers.Definitions.PolyRelaxation
import CORALean.NN.Layers.Definitions.PolySampling
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Definitions.ReluLayer
import CORALean.NN.Layers.Definitions.ReshapeLayer
import CORALean.NN.Layers.Definitions.ScaleRounding
import CORALean.NN.Layers.Definitions.Sigmoid
import CORALean.NN.Layers.Definitions.SigmoidLayer
import CORALean.NN.Layers.Definitions.SigmoidNetworks
import CORALean.NN.Layers.Definitions.SigmoidPoly
import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
import CORALean.NN.Layers.Definitions.SigmoidPolyLayer
import CORALean.NN.Layers.Definitions.SigmoidRelaxation
import CORALean.NN.Layers.Definitions.Softmax
import CORALean.NN.Layers.Definitions.SoftmaxExactLayer
import CORALean.NN.Layers.Definitions.SoftmaxLayer
import CORALean.NN.Layers.Definitions.Softplus
import CORALean.NN.Layers.Definitions.SoftplusBox
import CORALean.NN.Layers.Definitions.SoundLayer
import CORALean.NN.Layers.Definitions.TanhLayer
import CORALean.NN.Layers.Definitions.TanhRelaxation
import CORALean.NN.Layers.Definitions.RootRelaxation
import CORALean.NN.Layers.Definitions.WindowMax
import CORALean.NN.Layers.Definitions.SShape

/-!
# What the standard layers mean, collected

**What a layer is handed.** `Relaxation`, `Enclosure`, `ScaleRounding` and `PolyRelaxation` are
what an activation has to supply, each with the `Sound` predicate that ties it to `σ`.

**The functions over ℝ.** `Relu`, `WindowMax`, `BatchNorm`, `Sigmoid`, `Softmax`, `InvSqrt` and
`EvalPoly` are what the layers enclose, never what they run.

**Exact relaxations.** `SigmoidRelaxation`, `TanhRelaxation`, `InvSqrtRelaxation` and `Softmax`'s
layer are the generic constructors at `Enclosure.exact`, `Real.exp` being the one input no scalar
evaluates. The exact polynomial pipeline — `PolySampling`, `PolyDerivBound`, `PolyOfSampling`,
`PolyFit`, `PolyAffineConj`, `PolyFamily`, `SigmoidPoly`, `SigmoidPolyFamily` — fits by least
squares and chooses by existence, and `ActivationPoly`, `ActivationPolyRefinable` and
`SigmoidNetworks` are the exact layers and networks it drives to convergence.

**Layer kinds.** `LinearLayer` through `SigmoidPolyLayer` are the weights of each standard kind,
its `Enclose` instance in `Instances.lean`; `SoftmaxExactLayer` and `ActivationPolyExactLayer` are
the two exact ones, their instances here, being noncomputable.
-/
