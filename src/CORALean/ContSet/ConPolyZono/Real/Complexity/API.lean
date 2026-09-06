import CORALean.ContSet.ConPolyZono.Real.Complexity.And
import CORALean.ContSet.ConPolyZono.Real.Complexity.Plus
import CORALean.ContSet.ConPolyZono.Real.Complexity.Mtimes
import CORALean.ContSet.ConPolyZono.Real.Complexity.Compact
import CORALean.ContSet.ConPolyZono.Real.Complexity.QuadMap
import CORALean.ContSet.ConPolyZono.Real.Complexity.QuadMapBigO

/-!
# What `ConPolyZono` costs

The size of an operation's result as a function of its operands' — the three
`PolyZonotope` counts, factors `p`, dependent generators `h` and independent
generators `q`, plus the two this representation adds, constraints `m` and
constraint generators `s`. Each equality is `rfl` against the structure
instance in `Operations/`; `compact`'s three shrinking counts are bounds
instead, since compaction's whole job is to make them smaller.

`ConPolyZono.reduce*`'s existing order bounds are untouched here.

The number of scalar operations each operation costs is not yet stated here.

`quadMap_h_isBigO` is the shape the rest of this directory should eventually
take: not a bare count, but the count's growth in `O`-notation, tied to the
operation through a family of growing operands. `quadMap` is the operation
whose count multiplies rather than adds, so it carries this directory's
O-statement rather than `and`, `plus`, `mtimes` or `compact`.
-/
