import CORALean.NN.Definitions.Chain
import CORALean.NN.Definitions.IntervalChain
import CORALean.NN.Definitions.MergeBucket
import CORALean.NN.Definitions.ReducibleNetwork
import CORALean.NN.Definitions.Reduction
import CORALean.NN.Definitions.RefinableLayer
import CORALean.NN.Definitions.RefinableNetwork
import CORALean.NN.Definitions.RefinableNetworkImage
import CORALean.NN.Definitions.Schedule
import CORALean.NN.Definitions.SmoothNetwork
import CORALean.NN.Definitions.WeightAcc
import CORALean.NN.Definitions.WeightLayer
import CORALean.NN.Definitions.WeightNetwork
import CORALean.NN.Definitions.InputOrderMethod
import CORALean.NN.Definitions.ActivationKind
import CORALean.NN.Definitions.ActivationKindFn
import CORALean.NN.Definitions.Cat
import CORALean.NN.Definitions.CatDomain
import CORALean.NN.Definitions.SetBasedLoss

/-!
# What a network means, collected

The types a network is assembled from and the propositions its guarantees are stated in, never
run: `Chain`, one exact function per layer; `RefinableLayer`, `RefinableNetwork` and its exact
`RefinableNetworkImage`, with `Schedule`, the refinement loop's state; `MergeBucket`, the
neuron-merging buckets; `ReducibleNetwork`, the form the reduction algorithms read and
write, with the instances `Φ` stands for; and `Reduction`'s `ReducesAt`, reducing many layers
soundly.
`Cat` and `CatDomain` are AI2's conditional affine form of a network and what an abstract
domain owes it.
-/
