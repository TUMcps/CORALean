module

public import CORALean.ContSet.LevelSet.Real.Theorems.Basic
public import CORALean.ContSet.LevelSet.Real.Theorems.MemConstruct
public import CORALean.ContSet.LevelSet.Real.Theorems.AndExact
public import CORALean.ContSet.LevelSet.Real.Theorems.ContainsIff
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds
public import CORALean.ContSet.LevelSet.Real.Theorems.PlusExact
public import CORALean.ContSet.LevelSet.Real.Theorems.NotExact
public import CORALean.ContSet.LevelSet.Real.Theorems.RestrictConstruct
public import CORALean.ContSet.LevelSet.Real.Theorems.SplitEqualityExact
public import CORALean.ContSet.LevelSet.Real.Theorems.MtimesExact
public import CORALean.ContSet.LevelSet.Real.Theorems.TaylorSeriesMem
public import CORALean.ContSet.LevelSet.Real.Theorems.IntersectLevelSetBoxSubset
public import CORALean.ContSet.LevelSet.Real.Theorems.IntersectLevelSetBoxExact
public import CORALean.ContSet.LevelSet.Real.Theorems.IntersectLevelSetBoxParabola
public import CORALean.ContSet.LevelSet.Real.Theorems.GuardIntersectSolvableSubset
public import CORALean.ContSet.LevelSet.Real.Theorems.GuardIntersectUnsolvableSubset
public import CORALean.ContSet.LevelSet.Real.Theorems.SolvedGuardSinOfNeZero
public import CORALean.ContSet.LevelSet.Real.Theorems.OutsideInvariantOfRangeBound
public import CORALean.ContSet.LevelSet.Real.Theorems.GuardDisjointOfRangeBound
public import CORALean.ContSet.LevelSet.Real.Theorems.IsIntersectingUniformOuter
public import CORALean.ContSet.LevelSet.Real.Theorems.IsIntersectingCellOuter
public import CORALean.ContSet.LevelSet.Real.Theorems.RepresentsaEmptySetSound
public import CORALean.ContSet.LevelSet.Real.Theorems.RepresentsaFullspaceSound
public import CORALean.ContSet.LevelSet.Real.Theorems.CompactExact
public import CORALean.ContSet.LevelSet.Real.Theorems.IsequalSound
public import CORALean.ContSet.LevelSet.Real.Theorems.TightenDomainLinearIsContractor

/-!
# What a level set guarantees, collected

Every operation on a level set here is exact: a level set is closed under intersection, preimage
and, for an invertible map or a translation, image, because each is a substitution in `f`. The
guard-intersection models are not level sets but Taylor models over a box, and what is proved of
them is an enclosure of the box cut by the guard, exact only in `IntersectLevelSetBoxExact`.
-/
