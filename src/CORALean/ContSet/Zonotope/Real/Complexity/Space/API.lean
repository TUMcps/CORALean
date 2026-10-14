module

public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.MatMul
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Bilin
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.ReduceBy
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.ReduceBox
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.BackReachAligned
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.ReduceScottStep
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.QuadMapTri
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.SetBasedNetForward

/-!
# How large `Zonotope`'s results are

The size of an operation's result as a function of its operands' — generator
count only, since a `Zonotope` has one generator block — so that a
reachability order bound built from these means something. Each theorem is
`rfl` against the structure instance in `Operations/`.

`reduce`'s bounds are inequalities, not equalities, and stay in
`Theorems/ReduceOrder.lean`: reduction is the one operation whose whole job is
to make the count smaller, so its statement is a bound rather than a count.
`reduceBox` splits on the same condition and stays here regardless: its count
is exact on both sides of the `if`, `n` or `0`, since `reduceByBox` fixes its
own count without reading how many generators it absorbed.

How many scalar operations an operation costs is the other kind of claim and
lives in `Complexity/Time/`: a size follows from a definition and a running cost does not,
so one is proved here and the other asserted there.

`bilin_h_isBigO` is the shape the rest of this directory should eventually
take: not a bare count, but the count's growth in `O`-notation, tied to the
operation through a family of growing operands.
-/
