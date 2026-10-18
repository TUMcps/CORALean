module

public import CORALean.ContSet.Zoo.Float.Theorems.DiagonalBlockSum
public import CORALean.ContSet.Zoo.Float.Theorems.IntervalOuter
public import CORALean.ContSet.Zoo.Float.Theorems.MinusOuter
public import CORALean.ContSet.Zoo.Float.Theorems.OfIntervalAttains
public import CORALean.ContSet.Zoo.Float.Theorems.OfIntervalEncloses
public import CORALean.ContSet.Zoo.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zoo.Float.Theorems.RdivideOuter
public import CORALean.ContSet.Zoo.Float.Theorems.TimesOuter
public import CORALean.ContSet.Zoo.Float.Theorems.UminusOuter
public import CORALean.ContSet.Zoo.Float.Theorems.Basic
public import CORALean.ContSet.Zoo.Float.Theorems.EnclosesIff

/-!
# Float zoos: the guarantees

A zoo is `SetIntersection` at its members (`Zoo.members`), so membership is that class's
`mem_construct`, unfolded once to the two members in `encloses_iff`. Everything else here is the
zoo's own: how its operations combine the Taylor models with each other and the intervals with
each other, which no theorem about an intersection of sets says.
-/
