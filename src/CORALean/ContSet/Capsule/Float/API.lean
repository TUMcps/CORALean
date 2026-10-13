module

public import CORALean.ContSet.Capsule.Float.Operations.PiStep
public import CORALean.ContSet.Capsule.Float.Operations.ArcBox
public import CORALean.ContSet.Capsule.Float.Operations.Vertices
public import CORALean.ContSet.Capsule.Float.Theorems.PiStepMem
public import CORALean.ContSet.Capsule.Float.Theorems.ArcBoxMem
public import CORALean.ContSet.Capsule.Float.Theorems.VerticesOuter
public import CORALean.ContSet.Capsule.Float.Theorems.VerticesPoint
public import CORALean.ContSet.Capsule.Float.Operations.IsDisjoint
public import CORALean.ContSet.Capsule.Float.Theorems.IsDisjointSound
public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Float.Operations.Origin
public import CORALean.ContSet.Capsule.Float.Operations.Empty
public import CORALean.ContSet.Capsule.Float.Operations.Center
public import CORALean.ContSet.Capsule.Float.Operations.Reduce
public import CORALean.ContSet.Capsule.Float.Operations.Reindex
public import CORALean.ContSet.Capsule.Float.Operations.Project
public import CORALean.ContSet.Capsule.Float.Operations.BoundDot
public import CORALean.ContSet.Capsule.Float.Operations.BoundDotUp
public import CORALean.ContSet.Capsule.Float.Operations.Radius
public import CORALean.ContSet.Capsule.Float.Operations.Plus
public import CORALean.ContSet.Capsule.Float.Operations.Mtimes
public import CORALean.ContSet.Capsule.Float.Operations.ConvHull
public import CORALean.ContSet.Capsule.Float.Operations.Enclose
public import CORALean.ContSet.Capsule.Float.Operations.EnclosePoints
public import CORALean.ContSet.Capsule.Float.Operations.Isequal
public import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Capsule.Float.Operations.RepresentsaOrigin
public import CORALean.ContSet.Capsule.Float.Operations.IsFullDim
public import CORALean.ContSet.Capsule.Float.Operations.ContainsPoint
public import CORALean.ContSet.Capsule.Float.Theorems.Convex
public import CORALean.ContSet.Capsule.Float.Theorems.IsCompact
public import CORALean.ContSet.Capsule.Float.Theorems.CentreMemConstructIff
public import CORALean.ContSet.Capsule.Float.Theorems.OriginExact
public import CORALean.ContSet.Capsule.Float.Theorems.EmptyExact
public import CORALean.ContSet.Capsule.Float.Theorems.ReduceOuter
public import CORALean.ContSet.Capsule.Float.Theorems.ReindexExact
public import CORALean.ContSet.Capsule.Float.Theorems.ProjectExact
public import CORALean.ContSet.Capsule.Float.Theorems.BoundDotLe
public import CORALean.ContSet.Capsule.Float.Theorems.RadiusLe
public import CORALean.ContSet.Capsule.Float.Theorems.PlusOuter
public import CORALean.ContSet.Capsule.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Capsule.Float.Theorems.ConvHullOuter
public import CORALean.ContSet.Capsule.Float.Theorems.EncloseOuter
public import CORALean.ContSet.Capsule.Float.Theorems.EnclosePointsMem
public import CORALean.ContSet.Capsule.Float.Theorems.IsequalSound
public import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointSound
public import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaOriginSound
public import CORALean.ContSet.Capsule.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.Capsule.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.Capsule.Float.Instances

/-!
# Capsules over a floating-point scalar, collected

The representation in `Capsule`, `origin`, `empty`, `center`, `reduce`, `reindex` and `project` in
`Operations`, their guarantees in `Theorems`, and the class instances in `Instances`. The box a
capsule is enclosed by, and every conversion through it, are in `Conversion/Float/Capsule_to_*`.
-/
