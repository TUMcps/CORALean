import CORALean.NN.Theorems.LinearWithErrorZero
import CORALean.NN.Theorems.MergeErrorSplit
import CORALean.NN.Theorems.NeuronMergingOuter
import CORALean.NN.Theorems.PropagateOuter
import CORALean.NN.Theorems.Robustness
import CORALean.NN.Theorems.Verified

/-!
# What a network's enclosure guarantees, collected

`PropagateOuter` is the induction over the graph, `Verified` what it buys when a
specification is checked on the result, and `Robustness` the specification a
classifier is usually checked against, together with the bounds that discharge
it.

`LinearWithErrorZero`, `NeuronMergingOuter` and `MergeErrorSplit` are the sound
network reduction by neuron merging [1]: a plain linear layer as the error-free
case of the adapted one, the single-bucket containment sound at every bucket,
and disjoint buckets' errors composing by Minkowski sum.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/
