module

public import CORALean.Global.Float.Instances.Dyadic.Operations.AddDown
public import CORALean.Global.Float.Instances.Dyadic.Operations.AddUp
public import CORALean.Global.Float.Instances.Dyadic.Operations.AlignExp
public import CORALean.Global.Float.Instances.Dyadic.Operations.AlignGuard
public import CORALean.Global.Float.Instances.Dyadic.Operations.CoarsenDown
public import CORALean.Global.Float.Instances.Dyadic.Operations.CoarsenUp
public import CORALean.Global.Float.Instances.Dyadic.Operations.DivDown
public import CORALean.Global.Float.Instances.Dyadic.Operations.DivUp
public import CORALean.Global.Float.Instances.Dyadic.Operations.ExactAdd
public import CORALean.Global.Float.Instances.Dyadic.Operations.ExactMul
public import CORALean.Global.Float.Instances.Dyadic.Operations.Half
public import CORALean.Global.Float.Instances.Dyadic.Operations.Le
public import CORALean.Global.Float.Instances.Dyadic.Operations.LeAligned
public import CORALean.Global.Float.Instances.Dyadic.Operations.LeShl
public import CORALean.Global.Float.Instances.Dyadic.Operations.LeShr
public import CORALean.Global.Float.Instances.Dyadic.Operations.Maximum
public import CORALean.Global.Float.Instances.Dyadic.Operations.Minimum
public import CORALean.Global.Float.Instances.Dyadic.Operations.MulDown
public import CORALean.Global.Float.Instances.Dyadic.Operations.MulUp
public import CORALean.Global.Float.Instances.Dyadic.Operations.Neg
public import CORALean.Global.Float.Instances.Dyadic.Operations.QuotDown
public import CORALean.Global.Float.Instances.Dyadic.Operations.QuotUp
public import CORALean.Global.Float.Instances.Dyadic.Operations.RoundDown
public import CORALean.Global.Float.Instances.Dyadic.Operations.RoundUp
public import CORALean.Global.Float.Instances.Dyadic.Operations.Shift
public import CORALean.Global.Float.Instances.Dyadic.Operations.ToRat

/-!
# Dyadic numbers at a fixed precision: the operations, collected

Every rounded operation is exact-then-round: `exactAdd`/`exactMul` may overflow `p` bits — a
product needs `2p` — so they are separate from `roundUp`/`roundDown`, which return to the grid
by shifting the mantissa right by `shift` bits, taking the floor or the ceiling. Division is the
exception, and the only operation with no exact step: a quotient of dyadics is not dyadic, so
`quotUp`/`quotDown` round while dividing, and `divUp`/`divDown` round a second time past that.
`le`/`minimum`/`maximum` are exact, needing no rounding; `neg`/`half` touch the mantissa or the
exponent alone. `toRat` is the exact decoding into ℚ, nothing rounded. `addUp`/`addDown` first
coarsen the operands (`coarsenUp`/`coarsenDown`), and `le` decides by sign when the exponents are
far apart, so that no alignment forms a huge power of two.
-/
