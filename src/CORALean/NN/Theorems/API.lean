import CORALean.NN.Theorems.PropagateOuter
import CORALean.NN.Theorems.Robustness
import CORALean.NN.Theorems.Verified

/-!
# What a network's enclosure guarantees, collected

`PropagateOuter` is the induction over the graph, `Verified` what it buys when a
specification is checked on the result, and `Robustness` the specification a
classifier is usually checked against, together with the bounds that discharge
it.
-/
