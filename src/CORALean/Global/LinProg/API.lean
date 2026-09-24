import CORALean.Global.LinProg.LinProg
import CORALean.Global.LinProg.Duality
import CORALean.Global.LinProg.Composition
import CORALean.Global.LinProg.Simplex

/-!
# Linear programming, collected

The one question a set representation is asked when it has to become another:
how far does it reach in a given direction? `SupportBound` is the answer plus
its reason, `Duality` produces reasons from a solver's dual solution,
`Composition` carries them across the set operations, and `Simplex` is the
solver — unverified, and the one thing here nothing else relies on being right.

The same bound stored in a scalar is `Global/Float/FloatBound`, with the scalar interface: a
bound is scalar-generic like everything else, and only its home keeps the floating-point scalar
out of reach of every `Real` file, matching `Global/API.lean`.
-/
