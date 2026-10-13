module

public import CORALean.ContSet.LevelSet.Real.Operations.And
public import CORALean.ContSet.LevelSet.Real.Operations.Contains
public import CORALean.ContSet.LevelSet.Real.Operations.Empty
public import CORALean.ContSet.LevelSet.Real.Operations.Inf
public import CORALean.ContSet.LevelSet.Real.Operations.Plus
public import CORALean.ContSet.LevelSet.Real.Operations.Test
public import CORALean.ContSet.LevelSet.Real.Operations.Lift
public import CORALean.ContSet.LevelSet.Real.Operations.Mtimes
public import CORALean.ContSet.LevelSet.Real.Operations.Not
public import CORALean.ContSet.LevelSet.Real.Operations.Restrict
public import CORALean.ContSet.LevelSet.Real.Operations.SplitEquality
public import CORALean.ContSet.LevelSet.Real.Operations.IntersectLevelSetBox
public import CORALean.ContSet.LevelSet.Real.Operations.GuardIntersectSolvable
public import CORALean.ContSet.LevelSet.Real.Operations.GuardIntersectUnsolvable
public import CORALean.ContSet.LevelSet.Real.Operations.IsIntersectingUniform
public import CORALean.ContSet.LevelSet.Real.Operations.IsIntersectingCell
public import CORALean.ContSet.LevelSet.Real.Operations.ContainsCellCora
public import CORALean.ContSet.LevelSet.Real.Operations.PotIntCora
public import CORALean.ContSet.LevelSet.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.LevelSet.Real.Operations.RepresentsaFullspace
public import CORALean.ContSet.LevelSet.Real.Operations.Compact
public import CORALean.ContSet.LevelSet.Real.Operations.Isequal
public import CORALean.ContSet.LevelSet.Real.Operations.LinearCoord
public import CORALean.ContSet.LevelSet.Real.Operations.LinearSweep
public import CORALean.ContSet.LevelSet.Real.Operations.TightenDomainLinear

/-!
# Level set operations, collected

CORA's `and_`, `contains_` (at a point), `Inf`, `empty`, `lift_` and `not`, and the image under an
invertible matrix and a translation, which CORA does not define. `intersectLevelSetBox` and the two
`guardIntersect…` models enclose a box cut by an equality constraint, as CORA's `and_` does
for a level set and a polynomial zonotope.
-/
