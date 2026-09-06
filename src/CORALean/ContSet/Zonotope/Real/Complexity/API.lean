import CORALean.ContSet.Zonotope.Real.Complexity.Plus
import CORALean.ContSet.Zonotope.Real.Complexity.LinComb
import CORALean.ContSet.Zonotope.Real.Complexity.Mtimes
import CORALean.ContSet.Zonotope.Real.Complexity.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Complexity.MtimesMatZonotope
import CORALean.ContSet.Zonotope.Real.Complexity.Bilin
import CORALean.ContSet.Zonotope.Real.Complexity.ReduceBy
import CORALean.ContSet.Zonotope.Real.Complexity.BilinBigO

/-!
# What `Zonotope` costs

The size of an operation's result as a function of its operands' — generator
count only, since a `Zonotope` has one generator block — so that a
reachability order bound built from these means something. Each theorem is
`rfl` against the structure instance in `Operations/`.

`reduce`'s bounds are inequalities, not equalities, and stay in
`Theorems/ReduceOrder.lean`: reduction is the one operation whose whole job is
to make the count smaller, so its statement is a bound rather than a count.

The number of scalar operations each operation costs is not yet stated here.

`bilin_h_isBigO` is the shape the rest of this directory should eventually
take: not a bare count, but the count's growth in `O`-notation, tied to the
operation through a family of growing operands.
-/
