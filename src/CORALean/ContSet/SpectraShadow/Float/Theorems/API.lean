import CORALean.ContSet.SpectraShadow.Float.Theorems.GenerateESumRepExact
import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero
import CORALean.ContSet.SpectraShadow.Float.Theorems.EmptyExact
import CORALean.ContSet.SpectraShadow.Float.Theorems.InfExact
import CORALean.ContSet.SpectraShadow.Float.Theorems.MtimesOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.PlusOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.ProjectOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.PadLeftOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.PadRightOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.CartProdOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.Convex
import CORALean.ContSet.SpectraShadow.Float.Theorems.ConstructSubsetAbsorb
import CORALean.ContSet.SpectraShadow.Float.Theorems.InterOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.LmiBlockDiagDiagonal
import CORALean.ContSet.SpectraShadow.Float.Theorems.TieInterOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.ContainsPointSound
import CORALean.ContSet.SpectraShadow.Float.Theorems.PosSemidefOfDiagDominant
import CORALean.ContSet.SpectraShadow.Float.Theorems.DualBoundLe
import CORALean.ContSet.SpectraShadow.Float.Theorems.IsBoundedSound
import CORALean.ContSet.SpectraShadow.Float.Theorems.MemBase
import CORALean.ContSet.SpectraShadow.Float.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.SpectraShadow.Float.Theorems.RepresentsaOriginSound
import CORALean.ContSet.SpectraShadow.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.SpectraShadow.Float.Theorems.ConeOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.ConvHullOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.OrOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.LinCombOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.PolytopeOuter

/-!
# What a float spectrahedral shadow guarantees, collected

Stated over the same sets of real points as the exact layer states them, the
rounding already inside `construct`. `plus` is an enclosure, the exact layer's
equation weakened by the centre's rounding; `mem_nominalSet_iff` is the reading
every enclosure proof starts from, and `toRealMat_blockDiag` how a stored block
diagonal reads; and `Inf_exact` and `empty_exact` are equations, nothing being stored that rounds;
`project_outer` an enclosure; and convexity holds unconditionally, the error
box being convex too.
-/
