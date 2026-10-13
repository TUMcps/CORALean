module

public import CORALean.Global.Float.Instances.Real.API
public import CORALean.Global.Float.Instances.Dyadic.API
public import CORALean.Global.Float.Instances.FixedPoint.API
public import CORALean.Global.Float.Instances.Binary64.API
public import CORALean.Global.Float.Instances.IEEE.API

/-!
# Models of `SoundFloatArithmetic`

ℝ, where rounding is trivial, `Dyadic p`, where it is not, `FixedPoint f`, the
same outward rounding at decimal digits rather than binary mantissa bits,
`IEEE fmt`, which rounds onto a real binary format's grid, subnormals included,
and native binary64, where the obligations are assumed rather than proved. More
than one instance is the point: an axiom that only a rounding arithmetic can
violate is invisible against ℝ alone, and what the hardware costs is invisible
against `Dyadic` alone.

`Binary64` is the only one of the five that assumes anything. A result that
reaches it is true of IEEE 754 binary64 on the assumptions its `Axioms` lists;
the same result at `Dyadic p`, `FixedPoint f` or `IEEE fmt` rests on nothing
beyond Lean's own axioms.

`Flint/` is deliberately not collected here: its rounded operations call FLINT,
so only an executable that links the C library may import it, and the library
elaborates it as a root of its own.
-/
