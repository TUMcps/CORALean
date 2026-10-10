import CORALean.ContSet.Zonotope.Real.Cost.Plus
import CORALean.ContSet.Zonotope.Real.Cost.LinComb
import CORALean.ContSet.Zonotope.Real.Cost.Mtimes
import CORALean.ContSet.Zonotope.Real.Cost.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Cost.Map
import CORALean.ContSet.Zonotope.Real.Cost.ReduceBy
import CORALean.ContSet.Zonotope.Real.Cost.ReduceGirard
import CORALean.ContSet.Zonotope.Real.Cost.CartProd
import CORALean.ContSet.Zonotope.Real.Cost.Abs
import CORALean.ContSet.Zonotope.Real.Cost.Shift
import CORALean.ContSet.Zonotope.Real.Cost.Rotate
import CORALean.ContSet.Zonotope.Real.Cost.Project
import CORALean.ContSet.Zonotope.Real.Cost.UnitIntervalMul
import CORALean.ContSet.Zonotope.Real.Cost.ScalarIntervalMul
import CORALean.ContSet.Zonotope.Real.Cost.ReduceCombastel
import CORALean.ContSet.Zonotope.Real.Cost.ReduceByBasis
import CORALean.ContSet.Zonotope.Real.Cost.ReducePCA
import CORALean.ContSet.Zonotope.Real.Cost.MinkDiffAligned
import CORALean.ContSet.Zonotope.Real.Cost.MinkDiffStretch
import CORALean.ContSet.Zonotope.Real.Cost.MinkDiffRep
import CORALean.ContSet.Zonotope.Real.Cost.Bilin
import CORALean.ContSet.Zonotope.Real.Cost.MtimesMatZonotope
import CORALean.ContSet.Zonotope.Real.Cost.QuadMap
import CORALean.ContSet.Zonotope.Real.Cost.ExhaustiveSearch
import CORALean.ContSet.Zonotope.Real.Cost.ExhaustiveSearchBigO
import CORALean.ContSet.Zonotope.Real.Cost.ExhaustiveSearchFilteredBigO

/-!
# What running `Zonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**: read off the definition by hand, since a Lean
`def` never says what computing it costs. `Complexity/` is the other kind of
claim, how large a *result* is, and a theorem. Each count is an upper bound and
monotone in the operand sizes, which is what lets `LinearSysDT.reachCost_le`
assemble out of these plus `Complexity/`'s sizes.

`mapCost` and `bilinCost` take what one application of their map costs as a
parameter; `mtimesCost` and `mtimesMatZonotopeCost` are them at known maps.
`reducePCACost` and `reduceByBasisCost` take the eigendecomposition's and the
basis inverse's price as parameters, the definitions naming no algorithm for
either.

Not counted: `reduceMethC` and `methCBasis`, which pick a basis by
`Classical.choose` over every embedding of `n` filtered generators, so a count
of the definition would be factorial and say nothing of CORA's `n + 8` choose
`n` search; `minkDiffOrEmpty` and `minkDiffGenRec`, a `choose` and a set
recursion; and `methodCBasis`, a sublist enumeration.
-/
