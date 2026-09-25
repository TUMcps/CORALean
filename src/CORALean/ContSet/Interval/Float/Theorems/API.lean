import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import CORALean.ContSet.Interval.Float.Theorems.MinkDiffInner
import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Float.Theorems.MtimesIsNonempty
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
import CORALean.ContSet.Interval.Float.Theorems.NonemptyHullIsNonempty
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.ReindexExact
import CORALean.ContSet.Interval.Float.Theorems.ReindexNominal
import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Interval.Float.Theorems.SubsetNonemptyHull

/-!
# What `Interval` guarantees

Stated exactly as `Real` states it, over the same sets of real points, and proved
the same way each time: the exact guarantee composed with the `aux_..._refines`
lemma beside it. No set-level reasoning is repeated here.

`MtimesIsNonempty` is the exception in shape: it says of the rounded box what the
exact one says of itself, there being no set inclusion to compose with.
-/
