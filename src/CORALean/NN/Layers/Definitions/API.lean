module

public import CORALean.NN.Layers.Definitions.ActivationLayer
public import CORALean.NN.Layers.Definitions.ActivationPoly
public import CORALean.NN.Layers.Definitions.ActivationPolyExactLayer
public import CORALean.NN.Layers.Definitions.ActivationPolyLayer
public import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
public import CORALean.NN.Layers.Definitions.AvgPoolLayer
public import CORALean.NN.Layers.Definitions.BatchNorm
public import CORALean.NN.Layers.Definitions.BatchNormLayer
public import CORALean.NN.Layers.Definitions.ConvLayer
public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.EvalPoly
public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Definitions.InvSqrt
public import CORALean.NN.Layers.Definitions.InvSqrtRelaxation
public import CORALean.NN.Layers.Definitions.LeakyRelu
public import CORALean.NN.Layers.Definitions.LinearWithErrorLayer
public import CORALean.NN.Layers.Definitions.MaxPoolLayer
public import CORALean.NN.Layers.Definitions.PolyAffineConj
public import CORALean.NN.Layers.Definitions.PolyDerivBound
public import CORALean.NN.Layers.Definitions.PolyFamily
public import CORALean.NN.Layers.Definitions.PolyFit
public import CORALean.NN.Layers.Definitions.PolyOfSampling
public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.NN.Layers.Definitions.PolySampling
public import CORALean.NN.Layers.Definitions.RegionPoly
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Layers.Definitions.ReluLayer
public import CORALean.NN.Layers.Definitions.ScaleRounding
public import CORALean.NN.Layers.Definitions.Sigmoid
public import CORALean.NN.Layers.Definitions.SigmoidLayer
public import CORALean.NN.Layers.Definitions.SigmoidNetworks
public import CORALean.NN.Layers.Definitions.SigmoidPoly
public import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
public import CORALean.NN.Layers.Definitions.SigmoidPolyLayer
public import CORALean.NN.Layers.Definitions.SigmoidRelaxation
public import CORALean.NN.Layers.Definitions.Softmax
public import CORALean.NN.Layers.Definitions.SoftmaxExactLayer
public import CORALean.NN.Layers.Definitions.SoftmaxLayer
public import CORALean.NN.Layers.Definitions.Softplus
public import CORALean.NN.Layers.Definitions.SoftplusBox
public import CORALean.NN.Layers.Definitions.SoundLayer
public import CORALean.NN.Layers.Definitions.StarSet
public import CORALean.NN.Layers.Definitions.StarSetFloat
public import CORALean.NN.Layers.Definitions.TanhLayer
public import CORALean.NN.Layers.Definitions.TanhRelaxation
public import CORALean.NN.Layers.Definitions.RootRelaxation
public import CORALean.NN.Layers.Definitions.TaylmArray
public import CORALean.NN.Layers.Definitions.WindowMax
public import CORALean.NN.Layers.Definitions.SShape
public import CORALean.NN.Layers.Definitions.DeepZRelu
public import CORALean.NN.Layers.Definitions.DeepZSShape
public import CORALean.NN.Layers.Definitions.SShapedPrinted
public import CORALean.NN.Layers.Definitions.ApproxError
public import CORALean.NN.Layers.Definitions.ApproxErrorRelaxation
public import CORALean.NN.Layers.Definitions.SecantSlope
public import CORALean.NN.Layers.Definitions.EncloseNonlinearPrinted

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

**DeepZ.** `DeepZRelu` and `DeepZSShape` are its transformers over ℝ, `SShapedPrinted` the
class its footnote defines. `EvaluateSinghNeuronCora` and `EvaluateSinghCora` are CORA's
`'singh'` neuron step and a two-neuron network run through it.
-/
