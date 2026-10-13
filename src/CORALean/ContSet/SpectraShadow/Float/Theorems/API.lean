module

public import CORALean.ContSet.SpectraShadow.Float.Theorems.GenerateESumRepExact
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero
public import CORALean.ContSet.SpectraShadow.Float.Theorems.EmptyExact
public import CORALean.ContSet.SpectraShadow.Float.Theorems.InfExact
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MtimesOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PlusOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ProjectOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PadLeftOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PadRightOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.CartProdOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.Convex
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ConstructSubsetAbsorb
public import CORALean.ContSet.SpectraShadow.Float.Theorems.InterOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.LmiBlockDiagDiagonal
public import CORALean.ContSet.SpectraShadow.Float.Theorems.TieInterOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PosSemidefOfDiagDominant
public import CORALean.ContSet.SpectraShadow.Float.Theorems.DualBoundLe
public import CORALean.ContSet.SpectraShadow.Float.Theorems.IsBoundedSound
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemBase
public import CORALean.ContSet.SpectraShadow.Float.Theorems.RepresentsaEmptySetSound
public import CORALean.ContSet.SpectraShadow.Float.Theorems.RepresentsaOriginSound
public import CORALean.ContSet.SpectraShadow.Float.Theorems.RepresentsaPointSound
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ConeOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ConvHullOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.OrOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.LinCombOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PolytopeOuter

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
