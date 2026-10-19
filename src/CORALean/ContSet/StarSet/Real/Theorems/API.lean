module

public import CORALean.ContSet.StarSet.Real.Theorems.Basic
public import CORALean.ContSet.StarSet.Real.Theorems.Convex
public import CORALean.ContSet.StarSet.Real.Theorems.LinPredConvex
public import CORALean.ContSet.StarSet.Real.Theorems.LinPredMemAddRowsIff
public import CORALean.ContSet.StarSet.Real.Theorems.LinPredMemSnocIff
public import CORALean.ContSet.StarSet.Real.Theorems.OfPredExact
public import CORALean.ContSet.StarSet.Real.Theorems.RowBoundsMem

/-!
# What a star set guarantees, collected

It is convex where its predicate is, CORA's predicate is, a predicate's star set denotes what the
predicate does, the star set of a point contains it, and a coordinate's bounds hold; the
predicate's own `snoc` and `addRows` admit what they should.
-/
