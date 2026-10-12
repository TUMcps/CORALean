import CORALean.ContSet.Interval.Real.Definitions.Hull
import CORALean.ContSet.Interval.Real.Definitions.RootBound
import CORALean.ContSet.Interval.Real.Definitions.BoxPlane
import CORALean.ContSet.Interval.Real.Definitions.IsBoundsContractor

/-!
# What an interval means beyond its own construction

`Hull` is the interval hull of a set, the smallest box containing it. `RootBound` is what a
root search owes a contractor narrowing one bound: no zero of the function on the far side.
`BoxPlane` is a box cut by a hyperplane: the plane, a point on an edge, an s-face's vertices.
-/
