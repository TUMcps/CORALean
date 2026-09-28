import CORALean.Global.Float.Instances.Real.API
import CORALean.Global.Float.Instances.Dyadic.API
import CORALean.Global.Float.Instances.FixedPoint.API
import CORALean.Global.Float.Instances.Binary64.API

/-!
# Models of `SoundFloatArithmetic`

ℝ, where rounding is trivial, `Dyadic p`, where it is not, `FixedPoint f`, the
same outward rounding at decimal digits rather than binary mantissa bits, and
native binary64, where it is not either and the obligations are assumed rather
than proved. More than one instance is the point: an axiom that only a
rounding arithmetic can violate is invisible against ℝ alone, and what the
hardware costs is invisible against `Dyadic` alone.

`Binary64` is the only one of the four that assumes anything. A result that
reaches it is true of IEEE 754 binary64 on the assumptions its `Axioms` lists;
the same result at `Dyadic p` or `FixedPoint f` rests on nothing beyond Lean's
own axioms.
-/
