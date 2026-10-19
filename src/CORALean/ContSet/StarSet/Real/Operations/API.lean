module

public import CORALean.ContSet.StarSet.Real.Operations.Basic
public import CORALean.ContSet.StarSet.Real.Operations.OfPoint
public import CORALean.ContSet.StarSet.Real.Operations.OfPred
public import CORALean.ContSet.StarSet.Real.Operations.RowBounds

/-!
# What a star set computes, collected

`ofPred`, a predicate as a star set through the identity basis; `ofPoint` and `rowBounds`, the
interval a coordinate lies in over the factor box, at CORA's predicate. The predicate's own
operations, which a layer stepping a star set builds its new predicate from (#174):
`LinPred.snoc`, one more factor in a given range, and `LinPred.addRows`, more rows.
-/
