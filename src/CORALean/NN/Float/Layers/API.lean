import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Float.Layers.ActivationPoly
import CORALean.NN.Float.Layers.ActivationPolyRefine
import CORALean.NN.Float.Layers.Convolution
import CORALean.NN.Float.Layers.Curvature
import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Float.Layers.Pooling
import CORALean.NN.Float.Layers.PolyDerivBound
import CORALean.NN.Float.Layers.PolyEval
import CORALean.NN.Float.Layers.PolyOfSampling
import CORALean.NN.Float.Layers.PolyRelaxationOfBracket
import CORALean.NN.Float.Layers.PolyRelaxationPad
import CORALean.NN.Float.Layers.PolySampling
import CORALean.NN.Float.Layers.ReLU
import CORALean.NN.Float.Layers.Sigmoid
import CORALean.NN.Float.Layers.SigmoidPoly
import CORALean.NN.Float.Layers.Softmax
import CORALean.NN.Float.Layers.Tanh

/-!
# The standard layers over a floating-point scalar, collected

Each rounds in as few places as it can. `Linear`, `Convolution` and max pooling
round nowhere, their weights being *placed* rather than summed and `mtimes`
charging its rounding to the representation's own error box. `Activation` rounds
once, widening `offset ± error` outward; `ReLU` and `Curvature` once or twice
more, a slope never being a correctness condition. `ActivationPoly` rounds
nowhere, its box being centred at zero.

`Sigmoid` and `Tanh` needed something new, in `Global/Float`: `expDown`, a
directed exponential out of `half`, `+` and `*`, and a `divUp`/`divDown` pair;
that same enclosure at a box's ends is the derivative bracket their slope comes
from. `Softmax` is where the exponential's asymmetry is paid for.

The polynomial pipeline is six files, `PolyEval` to `SigmoidPoly`: a fit
enclosed at a float, a grid *certified* rather than computed, a sampling bound
whose slack rounds up, a recentring that pays for its own rounding, the
derivative bound supplying `M`, and the sigmoid where it closes into a layer.

`Reshape` and `BatchNorm` have no file here: `Layer.reshape` carries no weights
and `Layer.batchNorm` is `Layer.linear` at a folded scale and shift.
`ActivationPolyRefine` is `ActivationPoly` at an order pattern; convergence has
no float counterpart, `PolyRelaxationPad` making the degrees agree regardless.
-/
