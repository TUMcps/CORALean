import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound
import CORALean.ContSet.LevelSet.Real.Definitions.Contractor
import CORALean.ContSet.LevelSet.Real.Definitions.TaylorSeries
import CORALean.ContSet.LevelSet.Real.Definitions.GradEnclosure

/-!
# What guard intersection with a level set is built from

The specifications a guard intersection computes with: range bounding, which detects that a set
leaves an invariant or meets a guard, a contractor, which shrinks a box to the guard, and the
Taylor series operator, whose remainder interval encloses a guard function's Lagrange term.
-/
