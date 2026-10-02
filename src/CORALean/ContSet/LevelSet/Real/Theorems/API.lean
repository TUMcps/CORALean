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

/-!
# What a level set guarantees, collected

Every operation here is exact: a level set is closed under intersection, preimage and, for an
invertible map or a translation, image, because each is a substitution in `f`.
-/
