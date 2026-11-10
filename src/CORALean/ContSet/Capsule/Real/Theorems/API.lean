module

public import CORALean.ContSet.Capsule.Real.Theorems.MemToSetIffNorm
public import CORALean.ContSet.Capsule.Real.Theorems.ContainsPointIff
public import CORALean.ContSet.Capsule.Real.Theorems.ContainsTableIff
public import CORALean.ContSet.Capsule.Real.Theorems.SegDistMem
public import CORALean.ContSet.Capsule.Real.Theorems.IsIntersectingIff
public import CORALean.ContSet.Capsule.Real.Theorems.ToSetEqEmpty
public import CORALean.ContSet.Capsule.Real.Theorems.ToSetEqAdd
public import CORALean.ContSet.Capsule.Real.Theorems.Convex
public import CORALean.ContSet.Capsule.Real.Theorems.IsCompact
public import CORALean.ContSet.Capsule.Real.Theorems.IsFullDimIff
public import CORALean.ContSet.Capsule.Real.Theorems.Basic
public import CORALean.ContSet.Capsule.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Capsule.Real.Theorems.CenterMemToSetIff
public import CORALean.ContSet.Capsule.Real.Theorems.ReindexExact
public import CORALean.ContSet.Capsule.Real.Theorems.NormSubCenterLe
public import CORALean.ContSet.Capsule.Real.Theorems.RadiusExact
public import CORALean.ContSet.Capsule.Real.Theorems.ProjectExact
public import CORALean.ContSet.Capsule.Real.Theorems.PlusOuterKeepLeft
public import CORALean.ContSet.Capsule.Real.Theorems.PlusOuter
public import CORALean.ContSet.Capsule.Real.Theorems.ToSetSubsetOfDistLe
public import CORALean.ContSet.Capsule.Real.Theorems.PlusVecExact
public import CORALean.ContSet.Capsule.Real.Theorems.MtimesOuter
public import CORALean.ContSet.Capsule.Real.Theorems.ConvHullOuter
public import CORALean.ContSet.Capsule.Real.Theorems.EncloseOuter
public import CORALean.ContSet.Capsule.Real.Theorems.RepresentsaPointIff
public import CORALean.ContSet.Capsule.Real.Theorems.RepresentsaOriginIff
public import CORALean.ContSet.Capsule.Real.Theorems.IsequalToSet
public import CORALean.ContSet.Capsule.Real.Theorems.EnclosePointsMem
public import CORALean.ContSet.Capsule.Real.Theorems.VerticesMemFrontier
public import CORALean.ContSet.Capsule.Real.Theorems.VolumeEq

/-!
# What a capsule guarantees, collected

`toSet_eq_empty` and `toSet_eq_add` are the shared case split, at
`C.r < 0` and `0 ≤ C.r`; `convex_toSet` and `isCompact_toSet` both
transfer their property from the segment and the ball that split produces.
`mem_ofPoint` needs neither: at `g = 0` and `r = 0` the defining bound holds
at any `t`.
-/
