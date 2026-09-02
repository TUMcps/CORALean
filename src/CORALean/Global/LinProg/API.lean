import CORALean.Global.LinProg.LinProg
import CORALean.Global.LinProg.Duality
import CORALean.Global.LinProg.Composition

/-!
# Linear programming, collected

The one question a set representation is asked when it has to become another:
how far does it reach in a given direction? `SupportBound` is the answer plus
its reason, `Duality` produces reasons from a solver's dual solution, and
`Composition` carries them across the set operations.

`Float/` is deliberately not collected here, matching `Global/API.lean`:
importing it would put the floating-point scalar in reach of every `Real` file.
-/
