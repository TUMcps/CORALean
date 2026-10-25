module

public import CORALean.NN.Graph.Complexity.Space.Theorems.API

/-!
# How large a graph layer's result is

The generator counts [1, Thm. 1] composes, one file per operation and read as a
table: `Conv` and `Pooling` move none of the three counts, both layers at a
known graph being one `PolyZonotope.map`; `MessagePassingEnclosure` is
[1, Prop. 4]'s cubic, `ConvUncertain` is [1, Prop. 5]'s product, and `GcnSteps`
unrolls those over a chain. Every count here but the three bounds is `rfl`
against a structure instance, as everywhere else under `Complexity/Space/`.

The two `BigO` files are where the counts become [1]'s own statements: `O(h³)`
for the message-passing enclosure and `O(h_e^(3κ'))` for `κ'` steps of it,
each tied to the operation through a family of edge sets rather than left as
arithmetic. The node count and the input set sit in the constant, which is what
makes the exponent the paper's claim about the *edges*.

What is not here is a running cost. A count follows from a definition and is
proved; what evaluating one costs does not, and would belong in a `Complexity/Time/`
beside this directory stated against `Global/Cost.lean`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/
