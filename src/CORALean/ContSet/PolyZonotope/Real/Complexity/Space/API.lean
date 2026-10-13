module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Plus
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.LinComb
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Map
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Mtimes
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.MtimesIntervalMat
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Bilin
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Mul
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.EvalPoly
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.EvalPolySort
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.PadFront
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.PadBack
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Space.Compact

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
