module

public import CORALean.NN.Definitions.Chain
public import CORALean.NN.Definitions.IntervalChain
public import CORALean.NN.Definitions.MergeBucket
public import CORALean.NN.Definitions.MinSuffExplanation
public import CORALean.NN.Definitions.MinSuffExplanationAbstract
public import CORALean.NN.Definitions.MinSuffExplanationExact
public import CORALean.NN.Definitions.Misclassified
public import CORALean.NN.Definitions.ReducibleNetwork
public import CORALean.NN.Definitions.Reduction
public import CORALean.NN.Definitions.RefinableLayer
public import CORALean.NN.Definitions.RefinableNetwork
public import CORALean.NN.Definitions.RefinableNetworkImage
public import CORALean.NN.Definitions.Schedule
public import CORALean.NN.Definitions.SmoothNetwork
public import CORALean.NN.Definitions.SuffExplanation
public import CORALean.NN.Definitions.SuffExplanationAbstract
public import CORALean.NN.Definitions.SuffExplanationExact
public import CORALean.NN.Definitions.WeightAcc
public import CORALean.NN.Definitions.WeightLayer
public import CORALean.NN.Definitions.WeightNetwork
public import CORALean.NN.Definitions.Basic
public import CORALean.NN.Definitions.ActivationKind
public import CORALean.NN.Definitions.Cat
public import CORALean.NN.Definitions.CatDomain
public import CORALean.NN.Definitions.SetBasedLoss
public import CORALean.NN.Definitions.IntervalChainFloat
public import CORALean.NN.Definitions.IntervalChainFloatSound

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
