import CORALean.NN.Definitions.Chain
import CORALean.NN.Definitions.MergeBucket
import CORALean.NN.Definitions.ReducibleNetwork
import CORALean.NN.Definitions.Reduction
import CORALean.NN.Definitions.RefinableLayer
import CORALean.NN.Definitions.RefinableNetwork
import CORALean.NN.Definitions.RefinableNetworkImage
import CORALean.NN.Definitions.Schedule

/-!
# What a network means, collected

The types a network is assembled from and the propositions its guarantees are stated in, never
run: `Chain`, one exact function per layer; `RefinableLayer`, `RefinableNetwork` and its exact
`RefinableNetworkImage`, with `Schedule`, the refinement loop's state; `MergeBucket`, the
neuron-merging buckets; `ReducibleNetwork`, the form the reduction algorithms read and
write, with the instances `Φ` stands for; and `Reduction`'s `ReducesAt`, reducing many layers
soundly.
-/
