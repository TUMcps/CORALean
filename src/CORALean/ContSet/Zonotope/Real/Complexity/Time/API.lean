import CORALean.ContSet.Zonotope.Real.Complexity.Time.Plus
import CORALean.ContSet.Zonotope.Real.Complexity.Time.LinComb
import CORALean.ContSet.Zonotope.Real.Complexity.Time.Mtimes
import CORALean.ContSet.Zonotope.Real.Complexity.Time.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Complexity.Time.Map
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceBy
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceGirard
import CORALean.ContSet.Zonotope.Real.Complexity.Time.CartProd
import CORALean.ContSet.Zonotope.Real.Complexity.Time.Abs
import CORALean.ContSet.Zonotope.Real.Complexity.Time.Shift
import CORALean.ContSet.Zonotope.Real.Complexity.Time.Rotate
import CORALean.ContSet.Zonotope.Real.Complexity.Time.Project
import CORALean.ContSet.Zonotope.Real.Complexity.Time.UnitIntervalMul
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ScalarIntervalMul
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceCombastel
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceByBasis
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReducePCA
import CORALean.ContSet.Zonotope.Real.Complexity.Time.MinkDiffAligned
import CORALean.ContSet.Zonotope.Real.Complexity.Time.MinkDiffStretch
import CORALean.ContSet.Zonotope.Real.Complexity.Time.MinkDiffRep
import CORALean.ContSet.Zonotope.Real.Complexity.Time.Bilin
import CORALean.ContSet.Zonotope.Real.Complexity.Time.MtimesMatZonotope
import CORALean.ContSet.Zonotope.Real.Complexity.Time.QuadMap
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ExhaustiveSearch
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ExhaustiveSearchFiltered
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ImageEnclosure
import CORALean.ContSet.Zonotope.Real.Complexity.Time.SetBasedNetForward
import CORALean.ContSet.Zonotope.Real.Complexity.Time.SetBasedTraining

/-!
# What running `Zonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**: read off the definition by hand, since a Lean
`def` never says what computing it costs. `Complexity/Space/` is the other kind of
claim, how large a *result* is, and a theorem. Each count is an upper bound and
monotone in the operand sizes, which is what lets `LinearSysDT.reachCost_le`
assemble out of these plus `Complexity/Space/`'s sizes.

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
