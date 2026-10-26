module

public import CORALean.ContSet.Capsule.Float.Operations.PiStep
public import CORALean.ContSet.Capsule.Float.Operations.ArcBox
public import CORALean.ContSet.Capsule.Float.Operations.Vertices
public import CORALean.ContSet.Capsule.Float.Theorems.VerticesOuter
public import CORALean.ContSet.Capsule.Float.Theorems.VerticesPoint
public import CORALean.ContSet.Capsule.Float.Operations.IsDisjoint
public import CORALean.ContSet.Capsule.Float.Theorems.IsDisjointSound
public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Float.Operations.Basic
public import CORALean.ContSet.Capsule.Float.Operations.AbsorbRounding
public import CORALean.ContSet.Capsule.Float.Operations.Reduce
public import CORALean.ContSet.Capsule.Float.Operations.Reindex
public import CORALean.ContSet.Capsule.Float.Operations.Project
public import CORALean.ContSet.Capsule.Float.Operations.BoundDot
public import CORALean.ContSet.Capsule.Float.Operations.BoundDotUp
public import CORALean.ContSet.Capsule.Float.Operations.Plus
public import CORALean.ContSet.Capsule.Float.Operations.Mtimes
public import CORALean.ContSet.Capsule.Float.Operations.ConvHull
public import CORALean.ContSet.Capsule.Float.Operations.Enclose
public import CORALean.ContSet.Capsule.Float.Operations.EnclosePoints
public import CORALean.ContSet.Capsule.Float.Operations.Isequal
public import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Capsule.Float.Operations.IsFullDim
public import CORALean.ContSet.Capsule.Float.Operations.ContainsPoint
public import CORALean.ContSet.Capsule.Float.Theorems.Basic
public import CORALean.ContSet.Capsule.Float.Theorems.MemConstructOfSplit
public import CORALean.ContSet.Capsule.Float.Theorems.SmulMemSymmetric
public import CORALean.ContSet.Capsule.Float.Theorems.ConstructEqNominal
public import CORALean.ContSet.Capsule.Float.Theorems.CenterMemConstructIff
public import CORALean.ContSet.Capsule.Float.Theorems.ReindexExact
public import CORALean.ContSet.Capsule.Float.Theorems.Norm2LeErrorNorm
public import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointParts
public import CORALean.ContSet.Capsule.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.Capsule.Float.Theorems.OriginExact
public import CORALean.ContSet.Capsule.Float.Theorems.EmptyExact
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
public import CORALean.ContSet.Capsule.Float.Operations.BallVol
public import CORALean.ContSet.Capsule.Float.Operations.Volume
public import CORALean.ContSet.Capsule.Float.Theorems.VolumeLe

/-!
# Capsules over a floating-point scalar, collected

The representation in `Capsule`, `origin`, `empty`, `center`, `reduce`, `reindex`, `project` and
`absorbRounding` in `Operations`, their guarantees in `Theorems`, and the class instances in
`Instances`. The box a capsule is enclosed by, and every conversion through it, are in
`Conversion/Float/Capsule_to_*`.
-/
