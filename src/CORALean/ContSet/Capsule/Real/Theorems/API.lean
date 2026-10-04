import CORALean.ContSet.Capsule.Real.Theorems.MemConstructIffNorm
import CORALean.ContSet.Capsule.Real.Theorems.ContainsPointIff
import CORALean.ContSet.Capsule.Real.Theorems.ContainsTableIff
import CORALean.ContSet.Capsule.Real.Theorems.ContainsTableCounterexample
import CORALean.ContSet.Capsule.Real.Theorems.SegDistMem
import CORALean.ContSet.Capsule.Real.Theorems.IsIntersectingIff
import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty
import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqAdd
import CORALean.ContSet.Capsule.Real.Theorems.Convex
import CORALean.ContSet.Capsule.Real.Theorems.IsCompact
import CORALean.ContSet.Capsule.Real.Theorems.IsFullDimIff
import CORALean.ContSet.Capsule.Real.Theorems.OfPointMem
import CORALean.ContSet.Capsule.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Capsule.Real.Theorems.CentreMemConstructIff
import CORALean.ContSet.Capsule.Real.Theorems.EmptyExact
import CORALean.ContSet.Capsule.Real.Theorems.ReindexExact
import CORALean.ContSet.Capsule.Real.Theorems.NormSubCentreLe
import CORALean.ContSet.Capsule.Real.Theorems.RadiusExact
import CORALean.ContSet.Capsule.Real.Theorems.ProjectExact
import CORALean.ContSet.Capsule.Real.Theorems.PlusOuterKeepLeft
import CORALean.ContSet.Capsule.Real.Theorems.PlusOuter
import CORALean.ContSet.Capsule.Real.Theorems.ConstructSubsetOfDistLe
import CORALean.ContSet.Capsule.Real.Theorems.PlusVecExact
import CORALean.ContSet.Capsule.Real.Theorems.MtimesOuter
import CORALean.ContSet.Capsule.Real.Theorems.MtimesCoraCounterexample
import CORALean.ContSet.Capsule.Real.Theorems.ConvHullOuter
import CORALean.ContSet.Capsule.Real.Theorems.EncloseOuter
import CORALean.ContSet.Capsule.Real.Theorems.EncloseCoraCounterexample
import CORALean.ContSet.Capsule.Real.Theorems.RepresentsaPointIff
import CORALean.ContSet.Capsule.Real.Theorems.RepresentsaOriginIff
import CORALean.ContSet.Capsule.Real.Theorems.IsequalConstruct
import CORALean.ContSet.Capsule.Real.Theorems.EnclosePointsMem
import CORALean.ContSet.Capsule.Real.Theorems.VerticesMemFrontier

/-!
# What a capsule guarantees, collected

`IsFullDimCora.lean` is deliberately not collected here: it states the CORA discrepancy at the
`ContSet` instance, which `Instances.lean` declares after importing this file.

`construct_eq_empty` and `construct_eq_add` are the shared case split, at
`C.r < 0` and `0 ≤ C.r`; `convex_construct` and `isCompact_construct` both
transfer their property from the segment and the ball that split produces.
`mem_ofPoint` needs neither: at `g = 0` and `r = 0` the defining bound holds
at any `t`.
-/
