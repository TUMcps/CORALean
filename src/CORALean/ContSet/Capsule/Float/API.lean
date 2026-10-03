import CORALean.ContSet.Capsule.Float.Capsule
import CORALean.ContSet.Capsule.Float.Operations.Origin
import CORALean.ContSet.Capsule.Float.Operations.Empty
import CORALean.ContSet.Capsule.Float.Operations.Center
import CORALean.ContSet.Capsule.Float.Operations.Reduce
import CORALean.ContSet.Capsule.Float.Operations.Reindex
import CORALean.ContSet.Capsule.Float.Operations.Project
import CORALean.ContSet.Capsule.Float.Operations.BoundDot
import CORALean.ContSet.Capsule.Float.Operations.Radius
import CORALean.ContSet.Capsule.Float.Operations.Plus
import CORALean.ContSet.Capsule.Float.Operations.Mtimes
import CORALean.ContSet.Capsule.Float.Operations.ConvHull
import CORALean.ContSet.Capsule.Float.Operations.Enclose
import CORALean.ContSet.Capsule.Float.Operations.EnclosePoints
import CORALean.ContSet.Capsule.Float.Operations.Isequal
import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint
import CORALean.ContSet.Capsule.Float.Operations.RepresentsaOrigin
import CORALean.ContSet.Capsule.Float.Operations.IsFullDim
import CORALean.ContSet.Capsule.Float.Operations.ContainsPoint
import CORALean.ContSet.Capsule.Float.Theorems.Convex
import CORALean.ContSet.Capsule.Float.Theorems.IsCompact
import CORALean.ContSet.Capsule.Float.Theorems.CentreMemConstructIff
import CORALean.ContSet.Capsule.Float.Theorems.OriginExact
import CORALean.ContSet.Capsule.Float.Theorems.EmptyExact
import CORALean.ContSet.Capsule.Float.Theorems.ReduceOuter
import CORALean.ContSet.Capsule.Float.Theorems.ReindexExact
import CORALean.ContSet.Capsule.Float.Theorems.ProjectExact
import CORALean.ContSet.Capsule.Float.Theorems.BoundDotLe
import CORALean.ContSet.Capsule.Float.Theorems.RadiusLe
import CORALean.ContSet.Capsule.Float.Theorems.PlusOuter
import CORALean.ContSet.Capsule.Float.Theorems.MtimesOuter
import CORALean.ContSet.Capsule.Float.Theorems.ConvHullOuter
import CORALean.ContSet.Capsule.Float.Theorems.EncloseOuter
import CORALean.ContSet.Capsule.Float.Theorems.EnclosePointsMem
import CORALean.ContSet.Capsule.Float.Theorems.IsequalSound
import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaOriginSound
import CORALean.ContSet.Capsule.Float.Theorems.IsFullDimSound
import CORALean.ContSet.Capsule.Float.Theorems.ContainsPointSound
import CORALean.ContSet.Capsule.Float.Instances

/-!
# Capsules over a floating-point scalar, collected

The representation in `Capsule`, `origin`, `empty`, `center`, `reduce`, `reindex` and `project` in
`Operations`, their guarantees in `Theorems`, and the class instances in `Instances`. The box a
capsule is enclosed by, and every conversion through it, are in `Conversion/Float/Capsule_to_*`.
-/
