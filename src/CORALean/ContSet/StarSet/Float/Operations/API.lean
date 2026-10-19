module

public import CORALean.ContSet.StarSet.Float.Operations.AbsorbRounding
public import CORALean.ContSet.StarSet.Float.Operations.Basic
public import CORALean.ContSet.StarSet.Float.Operations.RowBounds

/-!
# What a float star set computes, collected

`absorbRounding`, the error box made into factors; `rowBounds`, the bounds of a coordinate over the
factor box, rounded outward. The predicate's own operations (#174), which a step builds its new
predicate from: `LinPred.snoc` and `LinPred.append`, more factors in given ranges, and
`LinPred.addRows`, more rows.
-/
