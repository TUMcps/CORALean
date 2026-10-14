module

public import CORALean.ContSet.HPolytope.Float.Operations.ProjectHighDim
public import CORALean.ContSet.HPolytope.Float.Operations.Isequal
public import CORALean.ContSet.HPolytope.Float.Operations.Not
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendRight
public import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
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
public import CORALean.ContSet.HPolytope.Float.Operations.MemEqsIff
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

/-!
# What the float `HPolytope` computes

Three groups.

Exactly and without arithmetic: `intersection` concatenates constraint lists, `padLeft`
and `padRight` widen the coefficient space with zeros, `halfScaledLeft` and its
mirror widen it by one weighting coordinate and halve every right-hand side into
it, and the constructors copy matrices. None of them rounds: halving and
negation are exact, and the rest computes nothing.

Rounding, and where it goes: `translate` moves each bound by what its row reads
off the shift, an inequality absorbing that upward and an equality outward at
both ends of its interval. This is what the interval right-hand side is for, and
the only operation here that needs it. `minkDiffOf` shifts each inequality bound
inward by a certified support bound of the subtrahend, rounding downward so the
result stays inside the exact difference.

Enclosing on chosen directions: `plusOf`, `linCombOf`, `mtimesOf` and
`intervalOf`, whose rows nobody can predict from the inputs' — `ofBounds` is
their shared shape and `DualBound` is where a halfspace description certifies a
direction for itself. `dualWeights` proposes the weights such a certificate needs,
by the exact simplex at ℚ on the floats' own values; it is the driver, never a proof.
-/
