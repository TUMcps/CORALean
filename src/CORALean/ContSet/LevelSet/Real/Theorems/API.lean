import CORALean.ContSet.LevelSet.Real.Theorems.ForallFinAdd
import CORALean.ContSet.LevelSet.Real.Theorems.MemConstruct
import CORALean.ContSet.LevelSet.Real.Theorems.AndExact
import CORALean.ContSet.LevelSet.Real.Theorems.ContainsIff
import CORALean.ContSet.LevelSet.Real.Theorems.ConstructEmpty
import CORALean.ContSet.LevelSet.Real.Theorems.ConstructInf
import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds
import CORALean.ContSet.LevelSet.Real.Theorems.PlusExact
import CORALean.ContSet.LevelSet.Real.Theorems.NotExact
import CORALean.ContSet.LevelSet.Real.Theorems.RestrictConstruct
import CORALean.ContSet.LevelSet.Real.Theorems.SplitEqualityExact
import CORALean.ContSet.LevelSet.Real.Theorems.SplitEqualityFstOp
import CORALean.ContSet.LevelSet.Real.Theorems.SplitEqualitySndOp
import CORALean.ContSet.LevelSet.Real.Theorems.LiftExact
import CORALean.ContSet.LevelSet.Real.Theorems.MtimesExact
import CORALean.ContSet.LevelSet.Real.Theorems.TaylorSeriesMem
import CORALean.ContSet.LevelSet.Real.Theorems.IntersectLevelSetBoxSubset
import CORALean.ContSet.LevelSet.Real.Theorems.IntersectLevelSetBoxExact
import CORALean.ContSet.LevelSet.Real.Theorems.IntersectLevelSetBoxCounterexample
import CORALean.ContSet.LevelSet.Real.Theorems.IntersectLevelSetBoxParabola
import CORALean.ContSet.LevelSet.Real.Theorems.GuardIntersectSolvableSubset
import CORALean.ContSet.LevelSet.Real.Theorems.GuardIntersectUnsolvableSubset
import CORALean.ContSet.LevelSet.Real.Theorems.GuardIntersectUnsolvableCounterexample
import CORALean.ContSet.LevelSet.Real.Theorems.SolvedGuardSinCounterexample
import CORALean.ContSet.LevelSet.Real.Theorems.SolvedGuardSinOfNeZero
import CORALean.ContSet.LevelSet.Real.Theorems.OutsideInvariantOfRangeBound
import CORALean.ContSet.LevelSet.Real.Theorems.GuardDisjointOfRangeBound
import CORALean.ContSet.LevelSet.Real.Theorems.IsIntersectingUniformOuter
import CORALean.ContSet.LevelSet.Real.Theorems.IsIntersectingCellOuter
import CORALean.ContSet.LevelSet.Real.Theorems.IsIntersectingCellCounterexample
import CORALean.ContSet.LevelSet.Real.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.LevelSet.Real.Theorems.RepresentsaFullspaceSound
import CORALean.ContSet.LevelSet.Real.Theorems.CompactExact
import CORALean.ContSet.LevelSet.Real.Theorems.IsequalSound
import CORALean.ContSet.LevelSet.Real.Theorems.IsequalCoraCounterexample

/-!
# What a level set guarantees, collected

Every operation on a level set here is exact: a level set is closed under intersection, preimage
and, for an invertible map or a translation, image, because each is a substitution in `f`. The
guard-intersection models are not level sets but Taylor models over a box, and what is proved of
them is an enclosure of the box cut by the guard, exact only in `IntersectLevelSetBoxExact`.
-/
