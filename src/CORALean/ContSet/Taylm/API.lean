import CORALean.ContSet.Taylm.Float.API
import CORALean.ContSet.Taylm.Real.API

/-!
# Taylor models

CORA's `taylm`: a polynomial over `[-1, 1]ⁿ` and a remainder interval, enclosing a
function rather than describing a set. Its arithmetic and the elementary functions keep the
enclosure, which is what makes it the representation for a nonlinear map's expansion; the
range set is read off by `interval` or a conversion.

The float layer refines the arithmetic, `interval`, `exp` and `log`. `sqrt` is exact layer
only: its float counterpart needs a directed `x^(1/2 - N - 1)` at the bottom of the range,
which `Global/Float` does not provide.
-/
