module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.API
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.API

/-!
# What running `Zonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**: read off the definition by hand, since a Lean
`def` never says what computing it costs. `Complexity/Space/` is the other kind of
claim, how large a *result* is, and a theorem. Each count is an upper bound and
monotone in the operand sizes, which is what lets `LinearSysDT.reachCost_le`
assemble out of these plus `Complexity/Space/`'s sizes. A count is the arithmetic and one
write per scalar of the result, so `plusCost` takes the operands' generator counts.

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
