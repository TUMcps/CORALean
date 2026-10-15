module

public import CORALean.Global.SupportFunction.SupportFunction
public import CORALean.Global.SupportFunction.Composition

/-!
# Bounds on a support function, collected

The one question a set representation is asked when it has to become another:
how far does it reach in a given direction? `SupportBound` is the answer plus
its reason, `SupportWitness` the attained value with its point, and
`Composition` carries both across the set operations. The bounds are produced
by closed forms of each representation, by composition, and by linear
programming duality (`Global/LinProg/Duality`); none of these is the only source.

The same bound stored in a scalar is `Global/Float/FloatBound`, with the scalar interface: a
bound is scalar-generic like everything else, and only its home keeps the floating-point scalar
out of reach of every `Real` file, matching `Global/API.lean`.
-/
