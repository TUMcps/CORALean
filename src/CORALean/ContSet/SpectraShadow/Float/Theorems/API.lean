import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero
import CORALean.ContSet.SpectraShadow.Float.Theorems.PlusOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.Convex

/-!
# What a float spectrahedral shadow guarantees, collected

Stated over the same sets of real points as the exact layer states them, the
rounding already inside `construct`. `plus` is an enclosure, the exact layer's
equation weakened by the centre's rounding; `mem_nominalSet_iff` is the reading
every enclosure proof starts from, and `toRealMat_blockDiag` how a stored block
diagonal reads; and convexity holds unconditionally, the error
box being convex too.
-/
