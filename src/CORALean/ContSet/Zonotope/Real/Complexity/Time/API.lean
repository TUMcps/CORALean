module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Plus
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.LinComb
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Mtimes
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Map
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceBy
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceGirard
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.CartProd
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Abs
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Shift
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Rotate
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Project
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.UnitIntervalMul
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ScalarIntervalMul
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceCombastel
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceByBasis
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReducePCA
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.MinkDiffAligned
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.MinkDiffStretch
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.MinkDiffRep
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Bilin
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.MtimesMatZonotope
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.QuadMap
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ExhaustiveSearch
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ExhaustiveSearchFiltered
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.ImageEnclosure
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.SetBasedNetForward
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.SetBasedTraining

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
