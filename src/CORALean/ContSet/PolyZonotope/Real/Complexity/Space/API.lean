import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Plus
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.LinComb
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Map
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.MtimesIntervalMat
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Bilin
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Mul
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.EvalPoly
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.EvalPolySort
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.PadFront
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.PadBack
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Dependent
import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Compact

/-!
# How large `PolyZonotope`'s results are

The size of an operation's result as a function of its operands' — all three
counts, factors `p`, dependent generators `h` and independent generators `q`,
since different operations move different ones. Every theorem here but
`Compact.lean`'s is `rfl` against the structure instance in `Operations/`.

`reduce`'s bounds are inequalities, not equalities, and stay in
`Theorems/ReduceOrder.lean` and `Theorems/ReduceGirardOrderLe.lean`: reduction
is the one operation whose whole job is to make a count smaller, so its
statement is a bound rather than a count. `Compact.lean` is a bound for the
same reason and stays here, being about sizes and nothing else.

How many scalar operations an operation costs is the other kind of claim and
lives in `Complexity/Time/`: a size follows from a definition and a running cost does not,
so one is proved here and the other asserted there.

`bilin_h_isBigO` is the shape the rest of this directory should eventually
take: not a bare count, but the count's growth in `O`-notation, tied to the
operation through a family of growing operands.
-/
