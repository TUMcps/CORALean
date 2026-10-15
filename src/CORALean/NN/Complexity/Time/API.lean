module

public import CORALean.NN.Complexity.Time.Operations.API
public import CORALean.NN.Complexity.Time.Theorems.API

/-!
# What running a network's `enclose` costs

Scalar-operation counts against `Global/Cost.lean`'s model, asserted rather
than proved: `NeuralNetwork.encloseCost` mirrors `enclose`'s own recursion,
one layer's cost per layer, at a per-layer bound the caller supplies — no
representation-agnostic file can price a specific layer, `Layer` storing
`enclose` and nothing else.

`Complexity/Space/` does not exist here for the same reason: how many generators a
layer's output carries depends on which layer it is — an activation layer's
relaxation, above all — so no size fact holds for `enclose` in general either.
`NeurNetContrSysDT/Complexity/Time/` is where a caller commits to a representation and a
per-layer bound, and assembles a run's cost from this file and `ContSet/`'s.
-/
