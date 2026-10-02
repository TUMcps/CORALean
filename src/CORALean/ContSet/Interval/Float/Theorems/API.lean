import CORALean.ContSet.Interval.Float.Theorems.BoundDotLe
import CORALean.ContSet.Interval.Float.Theorems.ContractHalfspaceOuter
import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
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
import CORALean.ContSet.Interval.Float.Theorems.UminusExact
import CORALean.ContSet.Interval.Float.Theorems.UplusExact
import CORALean.ContSet.Interval.Float.Theorems.MinusOuter
import CORALean.ContSet.Interval.Float.Theorems.InfimumMemConstruct
import CORALean.ContSet.Interval.Float.Theorems.IsCompact
import CORALean.ContSet.Interval.Float.Theorems.SupremumMemConstruct
import CORALean.ContSet.Interval.Float.Theorems.OrOuter
import CORALean.ContSet.Interval.Float.Theorems.ConvHullOuter
import CORALean.ContSet.Interval.Float.Theorems.EnclosePointsOuter
import CORALean.ContSet.Interval.Float.Theorems.OriginExact
import CORALean.ContSet.Interval.Float.Theorems.AbsExact
import CORALean.ContSet.Interval.Float.Theorems.EmptyExact
import CORALean.ContSet.Interval.Float.Theorems.ExpOuter
import CORALean.ContSet.Interval.Float.Theorems.LogOuter
import CORALean.ContSet.Interval.Float.Theorems.SignOuter
import CORALean.ContSet.Interval.Float.Theorems.LeSound
import CORALean.ContSet.Interval.Float.Theorems.LtSound
import CORALean.ContSet.Interval.Float.Theorems.ProjectHighDimOuter
import CORALean.ContSet.Interval.Float.Theorems.ProjectOuter
import CORALean.ContSet.Interval.Float.Theorems.RepresentsaEmptySetSound
import CORALean.ContSet.Interval.Float.Theorems.RepresentsaOriginSound
import CORALean.ContSet.Interval.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.Interval.Float.Theorems.TimesOuter
import CORALean.ContSet.Interval.Float.Theorems.IsFullDimSound
import CORALean.ContSet.Interval.Float.Theorems.MaxExact
import CORALean.ContSet.Interval.Float.Theorems.MinExact
import CORALean.ContSet.Interval.Float.Theorems.IsequalSound
import CORALean.ContSet.Interval.Float.Theorems.TransposeExact
import CORALean.ContSet.Interval.Float.Theorems.CtransposeExact
import CORALean.ContSet.Interval.Float.Theorems.DiagExact
import CORALean.ContSet.Interval.Float.Theorems.DiagVecExact
import CORALean.ContSet.Interval.Float.Theorems.MaskExact
import CORALean.ContSet.Interval.Float.Theorems.TrilExact
import CORALean.ContSet.Interval.Float.Theorems.TriuExact
import CORALean.ContSet.Interval.Float.Theorems.HorzcatExact
import CORALean.ContSet.Interval.Float.Theorems.VertcatExact
import CORALean.ContSet.Interval.Float.Theorems.CenterOuter
import CORALean.ContSet.Interval.Float.Theorems.RadiusOuter
import CORALean.ContSet.Interval.Float.Theorems.Sum1Outer
import CORALean.ContSet.Interval.Float.Theorems.Sum2Outer
import CORALean.ContSet.Interval.Float.Theorems.VolumeOuter
import CORALean.ContSet.Interval.Float.Theorems.SplitAtCover
import CORALean.ContSet.Interval.Float.Theorems.CenterGe
import CORALean.ContSet.Interval.Float.Theorems.CenterLoLe
import CORALean.ContSet.Interval.Float.Theorems.Sum1OuterImage
import CORALean.ContSet.Interval.Float.Theorems.Sum2OuterImage
import CORALean.ContSet.Interval.Float.Theorems.VolumeNominalLe
import CORALean.ContSet.Interval.Float.Theorems.NormNominalLe
import CORALean.ContSet.Interval.Float.Theorems.NormLe
import CORALean.ContSet.Interval.Float.Theorems.Radius2NominalLe
import CORALean.ContSet.Interval.Float.Theorems.Norm2SubCenterLe
import CORALean.ContSet.Interval.Float.Theorems.Prod1Outer
import CORALean.ContSet.Interval.Float.Theorems.PartitionCover
import CORALean.ContSet.Interval.Float.Theorems.PartitionPiece
import CORALean.ContSet.Interval.Float.Theorems.EnlargeOuter
import CORALean.ContSet.Interval.Float.Theorems.RecipOuter
import CORALean.ContSet.Interval.Float.Theorems.RdivideOuter
import CORALean.ContSet.Interval.Float.Theorems.MrdivideOuter
import CORALean.ContSet.Interval.Float.Theorems.OfCenterRadiusOuter
import CORALean.ContSet.Interval.Float.Theorems.QuadMapOuter

/-!
# What `Interval` guarantees

Stated exactly as `Real` states it, over the same sets of real points, and proved
the same way each time: the exact guarantee composed with the `aux_..._refines`
lemma beside it. No set-level reasoning is repeated here.

`MtimesIsNonempty` is the exception in shape: it says of the rounded box what the
exact one says of itself, there being no set inclusion to compose with.

The same for `uminus`, `uplus`, `minus`, `infimum`, `supremum`, `or`, `convHull_`,
`enclosePoints` and `origin`, composed with the exact layer.

The same for `le`, `lt`, `empty`, `representsa_*`, `exp`, `abs`, `times`, `project` and
`projectHighDim_`; `exp_outer` keeps `expUp`'s range hypothesis.

The same for `max`, `min` (exact, under nonemptiness of the readings), `isequal` (sound when
`true`) and `transpose`, `ctranspose` (exact).

The same for `center`, `rad`, `sum`, `volume_`, `split`, `norm_` and `radius`: each bounds the
exact layer's value in the direction its rounding goes. `norm_` and `radius` take a caller's `σ`
with `normSq ≤ σ·σ`.
-/
