import CORALean.ContSet.HPolytope.Float.Operations.ProjectHighDim
import CORALean.ContSet.HPolytope.Float.Operations.Isequal
import CORALean.ContSet.HPolytope.Float.Operations.Not
import CORALean.ContSet.HPolytope.Float.Operations.Intersection
import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendRight
import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
import CORALean.ContSet.HPolytope.Float.Operations.IntersectionExact
import CORALean.ContSet.HPolytope.Float.Operations.PlusOf
import CORALean.ContSet.HPolytope.Float.Operations.LinCombOf
import CORALean.ContSet.HPolytope.Float.Operations.MtimesOf
import CORALean.ContSet.HPolytope.Float.Operations.DualBound
import CORALean.ContSet.HPolytope.Float.Operations.DualWeights
import CORALean.ContSet.HPolytope.Float.Operations.RowLin
import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
import CORALean.ContSet.HPolytope.Float.Operations.SubsetOfBounds
import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
import CORALean.ContSet.HPolytope.Float.Operations.Eqs
import CORALean.ContSet.HPolytope.Float.Operations.Fullspace
import CORALean.ContSet.HPolytope.Float.Operations.MemFullspace
import CORALean.ContSet.HPolytope.Float.Operations.MemIneqsIff
import CORALean.ContSet.HPolytope.Float.Operations.MemEqsIff
import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
import CORALean.ContSet.HPolytope.Float.Operations.PadRight
import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadLeft
import CORALean.ContSet.HPolytope.Float.Operations.MulVecPadRight
import CORALean.ContSet.HPolytope.Float.Operations.MemPadLeftIff
import CORALean.ContSet.HPolytope.Float.Operations.MemPadRightIff
import CORALean.ContSet.HPolytope.Float.Operations.UnitBox
import CORALean.ContSet.HPolytope.Float.Operations.MemUnitBoxIff
import CORALean.ContSet.HPolytope.Float.Operations.MulVecSingle
import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLast
import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
import CORALean.ContSet.HPolytope.Float.Operations.SmulMemHalfScaledLeft
import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
import CORALean.ContSet.HPolytope.Float.Operations.SmulMemHalfScaledRight
import CORALean.ContSet.HPolytope.Float.Operations.Translate
import CORALean.ContSet.HPolytope.Float.Operations.UnitBox
import CORALean.ContSet.HPolytope.Float.Operations.MemUnitBoxIff
import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLast
import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
import CORALean.ContSet.HPolytope.Float.Operations.SmulMemHalfScaledLeft
import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
import CORALean.ContSet.HPolytope.Float.Operations.SmulMemHalfScaledRight
import CORALean.ContSet.HPolytope.Float.Operations.TranslateOuter
import CORALean.ContSet.HPolytope.Float.Operations.Minus
import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
import CORALean.ContSet.HPolytope.Float.Operations.EmptySet
import CORALean.ContSet.HPolytope.Float.Operations.CartProd
import CORALean.ContSet.HPolytope.Float.Operations.Origin
import CORALean.ContSet.HPolytope.Float.Operations.LiftCols
import CORALean.ContSet.HPolytope.Float.Operations.MulVecLiftCols
import CORALean.ContSet.HPolytope.Float.Operations.Lift
import CORALean.ContSet.HPolytope.Float.Operations.RepresentsaFullspace
import CORALean.ContSet.HPolytope.Float.Operations.RowScale
import CORALean.ContSet.HPolytope.Float.Operations.ReduceOverDomain
import CORALean.ContSet.HPolytope.Float.Operations.EmptyWeights
import CORALean.ContSet.HPolytope.Float.Operations.IsFullDim
import CORALean.ContSet.HPolytope.Float.Operations.RecipUp
import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevLo
import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevHi
import CORALean.ContSet.HPolytope.Float.Operations.ScaleRows
import CORALean.ContSet.HPolytope.Float.Operations.NormalizeRows
import CORALean.ContSet.HPolytope.Float.Operations.NormalizeConstraints
import CORALean.ContSet.HPolytope.Float.Operations.EqScalar
import CORALean.ContSet.HPolytope.Float.Operations.Restrict
import CORALean.ContSet.HPolytope.Float.Operations.IsZeroVec
import CORALean.ContSet.HPolytope.Float.Operations.DropZeros
import CORALean.ContSet.HPolytope.Float.Operations.CompactZeros
import CORALean.ContSet.HPolytope.Float.Operations.EqVec
import CORALean.ContSet.HPolytope.Float.Operations.DropAligned
import CORALean.ContSet.HPolytope.Float.Operations.CompactAlignedIneq
import CORALean.ContSet.HPolytope.Float.Operations.IsInvertedPair
import CORALean.ContSet.HPolytope.Float.Operations.KeptRows
import CORALean.ContSet.HPolytope.Float.Operations.LeadRows
import CORALean.ContSet.HPolytope.Float.Operations.PairsToEq
import CORALean.ContSet.HPolytope.Float.Operations.CompactAtoAe

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
