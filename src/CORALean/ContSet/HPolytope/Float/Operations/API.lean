module

public import CORALean.ContSet.HPolytope.Float.Operations.ProjectHighDim
public import CORALean.ContSet.HPolytope.Float.Operations.Isequal
public import CORALean.ContSet.HPolytope.Float.Operations.Not
public import CORALean.ContSet.HPolytope.Float.Operations.AnchorEqs
public import CORALean.ContSet.HPolytope.Float.Operations.AnchorEqsInBox
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.MemEqsIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemIneqsIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsConstructIff
public import CORALean.ContSet.HPolytope.Float.Operations.Slab
public import CORALean.ContSet.HPolytope.Float.Operations.MemSlabNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemSlabIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemLiftNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.PlusOf
public import CORALean.ContSet.HPolytope.Float.Operations.LinCombOf
public import CORALean.ContSet.HPolytope.Float.Operations.MtimesOf
public import CORALean.ContSet.HPolytope.Float.Operations.DualBound
public import CORALean.ContSet.HPolytope.Float.Operations.DualWeights
public import CORALean.ContSet.HPolytope.Float.Operations.RowLin
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.Eqs
public import CORALean.ContSet.HPolytope.Float.Operations.Fullspace
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.PadRight
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadRight
public import CORALean.ContSet.HPolytope.Float.Operations.MemPadLeftIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemPadRightIff
public import CORALean.ContSet.HPolytope.Float.Operations.UnitBox
public import CORALean.ContSet.HPolytope.Float.Operations.MemUnitBoxIff
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecSingle
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLast
public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
public import CORALean.ContSet.HPolytope.Float.Operations.SmulMemHalfScaledLeft
public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
public import CORALean.ContSet.HPolytope.Float.Operations.SmulMemHalfScaledRight
public import CORALean.ContSet.HPolytope.Float.Operations.Translate
public import CORALean.ContSet.HPolytope.Float.Operations.TranslateOuter
public import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Float.Operations.EmptySet
public import CORALean.ContSet.HPolytope.Float.Operations.CartProd
public import CORALean.ContSet.HPolytope.Float.Operations.Origin
public import CORALean.ContSet.HPolytope.Float.Operations.LiftCols
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecLiftCols
public import CORALean.ContSet.HPolytope.Float.Operations.Lift
public import CORALean.ContSet.HPolytope.Float.Operations.RepresentsaFullspace
public import CORALean.ContSet.HPolytope.Float.Operations.RowScale
public import CORALean.ContSet.HPolytope.Float.Operations.ReduceOverDomain
public import CORALean.ContSet.HPolytope.Float.Operations.EmptyWeights
public import CORALean.ContSet.HPolytope.Float.Operations.IsFullDim
public import CORALean.ContSet.HPolytope.Float.Operations.RecipUp
public import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevLo
public import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevHi
public import CORALean.ContSet.HPolytope.Float.Operations.ScaleRows
public import CORALean.ContSet.HPolytope.Float.Operations.NormalizeRows
public import CORALean.ContSet.HPolytope.Float.Operations.NormalizeConstraints
public import CORALean.ContSet.HPolytope.Float.Operations.EqScalar
public import CORALean.ContSet.HPolytope.Float.Operations.Restrict
public import CORALean.ContSet.HPolytope.Float.Operations.DropZeros
public import CORALean.ContSet.HPolytope.Float.Operations.CompactZeros
public import CORALean.ContSet.HPolytope.Float.Operations.EqVec
public import CORALean.ContSet.HPolytope.Float.Operations.DropAligned
public import CORALean.ContSet.HPolytope.Float.Operations.CompactAlignedIneq
public import CORALean.ContSet.HPolytope.Float.Operations.IsInvertedPair
public import CORALean.ContSet.HPolytope.Float.Operations.KeptRows
public import CORALean.ContSet.HPolytope.Float.Operations.LeadRows
public import CORALean.ContSet.HPolytope.Float.Operations.PairsToEq
public import CORALean.ContSet.HPolytope.Float.Operations.CompactAtoAe
public import CORALean.ContSet.HPolytope.Float.Operations.ExcludesPoint
public import CORALean.ContSet.HPolytope.Float.Operations.Materialise

/-!
# What the float `HPolytope` computes

Exactly and without arithmetic: `stackRows` concatenates rows and slacks (the nominal intersection,
which reads no box), `padLeft`, `padRight` and `lift_` widen the coefficient space and carry the
box and the slacks along, `halfScaledLeft` and its mirror widen it by one weighting coordinate and
halve every right-hand side into it, and the constructors copy matrices. None of them rounds.

Moving the error box into the rows: `absorbRounding` raises each right-hand side by its slack and
the box's support in that row's direction and writes each equality as the two inequalities it
stands for, widened by its slack;
the normalizations of a polytope with a box and `not` read a polytope through it, a box not being
a halfspace.

Rounding, and where it goes: an inequality is raised; a rounded equality is kept, the certified step
onto it paid into the box (`anchorEqs`, which `intersection`, `translate` and `scaleRows` use;
`anchorEqsInBox` for unit-box coefficients), or written as two inequalities without a certificate.
`minkDiffOf` shifts each inequality bound inward by a certified support bound of the subtrahend,
rounding downward so the result stays inside the exact one.

Enclosing on chosen directions: `plusOf`, `linCombOf`, `mtimesOf` and `intervalOf`, whose rows
nobody can predict from the inputs' — `ofBounds` is their shared shape and `DualBound` is where
a halfspace description certifies a direction for itself. `dualWeights` proposes the weights such
a certificate needs, by the exact simplex at ℚ; it is the driver, never a proof.
-/
