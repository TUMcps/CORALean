module

public import CORALean.ContSet.StarSet.Real.Operations.OfPoint
public import CORALean.ContSet.StarSet.Real.Operations.OfPred
public import CORALean.ContSet.StarSet.Real.Operations.RowBounds

/-!
# What a star set computes, collected

`ofPred`, a predicate on a box as a star set through the identity basis; `ofPoint`, at CORA's
predicate; and `rowBounds`, the interval a coordinate lies in over the coefficient box. A layer
stepping a star set builds its new predicate with the predicate's own operations (#174).
-/
