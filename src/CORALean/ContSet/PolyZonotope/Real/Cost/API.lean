import CORALean.ContSet.PolyZonotope.Real.Cost.Plus
import CORALean.ContSet.PolyZonotope.Real.Cost.Map
import CORALean.ContSet.PolyZonotope.Real.Cost.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Cost.LinComb
import CORALean.ContSet.PolyZonotope.Real.Cost.Dependent
import CORALean.ContSet.PolyZonotope.Real.Cost.Bilin
import CORALean.ContSet.PolyZonotope.Real.Cost.Mul
import CORALean.ContSet.PolyZonotope.Real.Cost.QuadBilin
import CORALean.ContSet.PolyZonotope.Real.Cost.QuadMapDep
import CORALean.ContSet.PolyZonotope.Real.Cost.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Cost.Compact
import CORALean.ContSet.PolyZonotope.Real.Cost.ReduceBy
import CORALean.ContSet.PolyZonotope.Real.Cost.ReduceGirard
import CORALean.ContSet.PolyZonotope.Real.Cost.Reduce

/-!
# What running `PolyZonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one of them **asserted** — read off the operation's definition
by hand, never `rfl` against it. `Complexity/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

This is where a cost model earns its keep. `Complexity/Bilin.lean` proves the
result of a pairing carries `(h₁+1)(h₂+1)` generators, and `bilinCost` says
every one of them is computed, so `mul` and `quadMap` are quadratic in a count
that `plus` grows and only `reduce` brings down. `compactCost` is quadratic for
its own reason — a pairwise merge over exponent columns — which is why
`reduceCost` is the two squares added.

`bilinCost` and `mapCost` take the cost of one application of their map as an
argument, since a bound on an arbitrary linear or bilinear map is not something
this directory can have; `mtimesCost`, `mulCost` and `quadMapDepCost` are them
at a map whose count is known.

Each count is monotone in the operand sizes it takes, which is what lets a
caller substitute a bound on a size for the size.
-/
