module

public import CORALean.ContSet.Interval.Real.Definitions.Hull
public import CORALean.ContSet.Interval.Real.Definitions.RootBound
public import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
public import CORALean.ContSet.Interval.Real.Definitions.IsBoundsContractor
public import CORALean.ContSet.Interval.Real.Definitions.NormType
public import CORALean.ContSet.Interval.Real.Definitions.MatContains

/-!
# What an interval means beyond its own construction

`Hull` is the interval hull of a set, the smallest box containing it. `RootBound` is what a
root search owes a contractor narrowing one bound: no zero of the function on the far side.
`BoxPlane` is a box cut by a hyperplane: the plane, a point on an edge, an s-face's vertices.
-/
