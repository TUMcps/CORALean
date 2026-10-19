module

public import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound
public import CORALean.ContSet.LevelSet.Real.Definitions.Contractor
public import CORALean.ContSet.LevelSet.Real.Definitions.TaylorSeries
public import CORALean.ContSet.LevelSet.Real.Definitions.GradEnclosure
public import CORALean.ContSet.LevelSet.Real.Definitions.IsMetWithin

/-!
# What guard intersection with a level set is built from

The specifications a guard intersection computes with: range bounding, which detects that a set
leaves an invariant or meets a guard, a contractor, which shrinks a box to the guard, and the
Taylor series operator, whose remainder interval encloses a guard function's Lagrange term; and a
comparison met to within a slack, which a float constraint row records its rounding as.
-/
