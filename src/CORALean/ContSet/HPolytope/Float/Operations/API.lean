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
import CORALean.ContSet.HPolytope.Float.Operations.EmptySet

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
the only operation here that needs it.

Enclosing on chosen directions: `plusOf`, `linCombOf`, `mtimesOf` and
`intervalOf`, whose rows nobody can predict from the inputs' — `ofBounds` is
their shared shape and `DualBound` is where a halfspace description certifies a
direction for itself.
-/
