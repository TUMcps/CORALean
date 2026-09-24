import CORALean.NN.Layers.Definitions.ActivationPoly
import CORALean.NN.Layers.Definitions.ActivationPolyRefinable
import CORALean.NN.Layers.Definitions.BatchNorm
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.EvalPoly
import CORALean.NN.Layers.Definitions.InvSqrt
import CORALean.NN.Layers.Definitions.InvSqrtRelaxation
import CORALean.NN.Layers.Definitions.PolyAffineConj
import CORALean.NN.Layers.Definitions.PolyDerivBound
import CORALean.NN.Layers.Definitions.PolyFamily
import CORALean.NN.Layers.Definitions.PolyFit
import CORALean.NN.Layers.Definitions.PolyOfSampling
import CORALean.NN.Layers.Definitions.PolyRelaxation
import CORALean.NN.Layers.Definitions.PolySampling
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Definitions.ScaleRounding
import CORALean.NN.Layers.Definitions.Sigmoid
import CORALean.NN.Layers.Definitions.SigmoidNetworks
import CORALean.NN.Layers.Definitions.SigmoidPoly
import CORALean.NN.Layers.Definitions.SigmoidPolyFamily
import CORALean.NN.Layers.Definitions.SigmoidRelaxation
import CORALean.NN.Layers.Definitions.Softmax
import CORALean.NN.Layers.Definitions.TanhRelaxation
import CORALean.NN.Layers.Definitions.WindowMax

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
-/
