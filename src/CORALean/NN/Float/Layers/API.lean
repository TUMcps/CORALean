import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Float.Layers.ActivationPoly
import CORALean.NN.Float.Layers.ActivationPolyRefine
import CORALean.NN.Float.Layers.Convolution
import CORALean.NN.Float.Layers.Curvature
import CORALean.NN.Float.Layers.Linear
import CORALean.NN.Float.Layers.Pooling
import CORALean.NN.Float.Layers.PolyRelaxationPad
import CORALean.NN.Float.Layers.ReLU
import CORALean.NN.Float.Layers.Sigmoid
import CORALean.NN.Float.Layers.Softmax
import CORALean.NN.Float.Layers.Tanh

/-!
# The standard layers over a floating-point scalar, collected

Each rounds in as few places as it can, and two of the twelve are missing on
purpose. `Linear` rounds nowhere: `mtimes` and `plus` pay their own rounding into
the representation's error box. `Convolution` and max pooling inherit that, a
stencil matrix's entries being *placed* rather than summed.

`Activation` rounds in one place, widening `offset ± error` outward, `ReLU` in
one more and `Curvature` in two — a slope is never a correctness condition, so
each is clamped and left unrounded. `ActivationPoly` rounds nowhere, its box
being centred at zero. Max pooling is the same shape a window wider.

`Sigmoid` and `Tanh` needed something new, in `Global/Float`: `expDown`, a
directed exponential out of `half`, `+` and `*`, and a `divUp`/`divDown` pair;
that same enclosure, at a box's ends, is the derivative bracket their slope comes
from. `Softmax` is where the exponential's asymmetry is paid for: its lower bound
would need `expUp`, which is not total, so it takes one from the normalization.

`Reshape` and `BatchNorm` have no file here, and neither is an omission. `Layer.reshape` carries
no weights, so the exact constructor is already the float one; `Layer.batchNorm` is
`Layer.linear` at a folded scale and shift. `ActivationPolyRefine` is `ActivationPoly` at an
order pattern, `PolyRelaxationPad` making the neurons' degrees agree, and the loop's soundness
covers it unchanged; convergence is not, its own docstring saying why.
-/
