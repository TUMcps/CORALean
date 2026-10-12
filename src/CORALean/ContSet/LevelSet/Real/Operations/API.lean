import CORALean.ContSet.LevelSet.Real.Operations.And
import CORALean.ContSet.LevelSet.Real.Operations.Contains
import CORALean.ContSet.LevelSet.Real.Operations.Empty
import CORALean.ContSet.LevelSet.Real.Operations.Inf
import CORALean.ContSet.LevelSet.Real.Operations.Plus
import CORALean.ContSet.LevelSet.Real.Operations.Test
import CORALean.ContSet.LevelSet.Real.Operations.Lift
import CORALean.ContSet.LevelSet.Real.Operations.Mtimes
import CORALean.ContSet.LevelSet.Real.Operations.Not
import CORALean.ContSet.LevelSet.Real.Operations.Restrict
import CORALean.ContSet.LevelSet.Real.Operations.SplitEquality
import CORALean.ContSet.LevelSet.Real.Operations.IntersectLevelSetBox
import CORALean.ContSet.LevelSet.Real.Operations.GuardIntersectSolvable
import CORALean.ContSet.LevelSet.Real.Operations.GuardIntersectUnsolvable
import CORALean.ContSet.LevelSet.Real.Operations.IsIntersectingUniform
import CORALean.ContSet.LevelSet.Real.Operations.IsIntersectingCell
import CORALean.ContSet.LevelSet.Real.Operations.ContainsCellCora
import CORALean.ContSet.LevelSet.Real.Operations.PotIntCora
import CORALean.ContSet.LevelSet.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.LevelSet.Real.Operations.RepresentsaFullspace
import CORALean.ContSet.LevelSet.Real.Operations.Compact
import CORALean.ContSet.LevelSet.Real.Operations.Isequal
import CORALean.ContSet.LevelSet.Real.Operations.LinearCoord
import CORALean.ContSet.LevelSet.Real.Operations.LinearSweep
import CORALean.ContSet.LevelSet.Real.Operations.TightenDomainLinear

/-!
# Level set operations, collected

CORA's `and_`, `contains_` (at a point), `Inf`, `empty`, `lift_` and `not`, and the image under an
invertible matrix and a translation, which CORA does not define. `intersectLevelSetBox` and the two
`guardIntersect…` models enclose a box cut by an equality constraint, as CORA's `and_` does
for a level set and a polynomial zonotope.
-/
