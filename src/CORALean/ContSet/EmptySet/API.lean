module

public import CORALean.ContSet.EmptySet.Real.API

/-!
# The empty set

CORA's `emptySet`: `∅` in a stated dimension, as a representation rather than
as a degenerate value of another one.

It is the target a conversion reaches once a set has been shown empty, and
nothing converts into it yet. What an operation *returns* when its result may
be empty is `OptEmpty`, which keeps a representation beside the empty case.

Real layer only: the representation holds no scalar, so there is nothing a
float layer could round.
-/
