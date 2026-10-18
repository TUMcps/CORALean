module

public import CORALean.ContSet.Zoo.Real.Theorems.IntervalOuter
public import CORALean.ContSet.Zoo.Real.Theorems.MinusOuter
public import CORALean.ContSet.Zoo.Real.Theorems.PlusOuter
public import CORALean.ContSet.Zoo.Real.Theorems.RdivideOuter
public import CORALean.ContSet.Zoo.Real.Theorems.TimesOuter
public import CORALean.ContSet.Zoo.Real.Theorems.UminusOuter
public import CORALean.ContSet.Zoo.Real.Theorems.Basic
public import CORALean.ContSet.Zoo.Real.Theorems.EnclosesIff
public import CORALean.ContSet.Zoo.Real.Theorems.OfIntervalEncloses

/-!
# Zoos: the theorems

A zoo is `SetIntersection` at its members (`Zoo.members`), so membership is that class's
`mem_construct`, unfolded once to the two members in `encloses_iff`. Everything else here is the
zoo's own: how its operations combine the Taylor models with each other and the intervals with
each other, which no theorem about an intersection of sets says.
-/
