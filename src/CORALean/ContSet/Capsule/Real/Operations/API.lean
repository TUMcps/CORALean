module

public import CORALean.ContSet.Capsule.Real.Operations.ContainsPoint
public import CORALean.ContSet.Capsule.Real.Operations.SegDist
public import CORALean.ContSet.Capsule.Real.Operations.IsIntersecting
public import CORALean.ContSet.Capsule.Real.Operations.IsIntersectingCora
public import CORALean.ContSet.Capsule.Real.Operations.OfPoint
public import CORALean.ContSet.Capsule.Real.Operations.SupportBound
public import CORALean.ContSet.Capsule.Real.Operations.Empty
public import CORALean.ContSet.Capsule.Real.Operations.Reindex
public import CORALean.ContSet.Capsule.Real.Operations.Radius
public import CORALean.ContSet.Capsule.Real.Operations.Project
public import CORALean.ContSet.Capsule.Real.Operations.Plus
public import CORALean.ContSet.Capsule.Real.Operations.PlusVec
public import CORALean.ContSet.Capsule.Real.Operations.Mtimes
public import CORALean.ContSet.Capsule.Real.Operations.MtimesCora
public import CORALean.ContSet.Capsule.Real.Operations.ConvHull
public import CORALean.ContSet.Capsule.Real.Operations.ConvHullCora
public import CORALean.ContSet.Capsule.Real.Operations.Enclose
public import CORALean.ContSet.Capsule.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Capsule.Real.Operations.RepresentsaOrigin
public import CORALean.ContSet.Capsule.Real.Operations.Isequal
public import CORALean.ContSet.Capsule.Real.Operations.EnclosePoints
public import CORALean.ContSet.Capsule.Real.Operations.Vertices
public import CORALean.ContSet.Capsule.Real.Operations.Volume
public import CORALean.ContSet.Capsule.Real.Operations.RepresentsaHyperplaneCora

/-!
# What a capsule computes, collected

`ofPoint`: a capsule is closed under almost nothing, `Instances.lean` says
why, but a degenerate one — no direction, no radius — still names the point
it collapses to. `supportBound` answers any direction in closed form, the
segment and the ball each contributing their own term.
-/
