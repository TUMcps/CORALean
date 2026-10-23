module

public import CORALean.ContSet.HPolytope.Float.Operations.ProjectHighDim
public import CORALean.ContSet.HPolytope.Float.Operations.Isequal
public import CORALean.ContSet.HPolytope.Float.Operations.Not
public import CORALean.ContSet.HPolytope.Float.Operations.AnchorEqsInBox
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.BoxToSlack
public import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.Slab
public import CORALean.ContSet.HPolytope.Float.Operations.PlusOf
public import CORALean.ContSet.HPolytope.Float.Operations.LinCombOf
public import CORALean.ContSet.HPolytope.Float.Operations.MtimesOf
public import CORALean.ContSet.HPolytope.Float.Operations.DualBound
public import CORALean.ContSet.HPolytope.Float.Operations.DualWeights
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.Eqs
public import CORALean.ContSet.HPolytope.Float.Operations.Fullspace
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.HPolytope.Float.Operations.PadRight
public import CORALean.ContSet.HPolytope.Float.Operations.UnitBox
public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
public import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
public import CORALean.ContSet.HPolytope.Float.Operations.SetRhs
public import CORALean.ContSet.HPolytope.Float.Operations.RescaleCols
public import CORALean.ContSet.HPolytope.Float.Operations.KeepCols
public import CORALean.ContSet.HPolytope.Float.Operations.SelectCols
public import CORALean.ContSet.HPolytope.Float.Operations.ContainsOrigin
public import CORALean.ContSet.HPolytope.Float.Operations.IneqsContainBall
public import CORALean.ContSet.HPolytope.Float.Operations.IneqMargin
public import CORALean.ContSet.HPolytope.Float.Operations.EqsWithin
public import CORALean.ContSet.HPolytope.Float.Operations.Translate
public import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Float.Operations.EmptySet
public import CORALean.ContSet.HPolytope.Float.Operations.CartProd
public import CORALean.ContSet.HPolytope.Float.Operations.Origin
public import CORALean.ContSet.HPolytope.Float.Operations.LiftCols
public import CORALean.ContSet.HPolytope.Float.Operations.Lift
public import CORALean.ContSet.HPolytope.Float.Operations.RepresentsaFullspace
public import CORALean.ContSet.HPolytope.Float.Operations.RowScale
public import CORALean.ContSet.HPolytope.Float.Operations.ReduceOverDomain
public import CORALean.ContSet.HPolytope.Float.Operations.EmptyWeights
public import CORALean.ContSet.HPolytope.Float.Operations.IsFullDim
public import CORALean.ContSet.HPolytope.Float.Operations.RecipUp
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

Moving the error box into the rows: `absorbRounding` raises each bound by its slack and the box's
support along the row, each equality written as its two inequalities, the one place a slack enters
`b`; the normalizations and `not` read a polytope through it. `boxToSlack` moves the box into the
slacks instead, rows and bounds kept, which is what `intersection` stacks.

Rounding, and where it goes (#218): an operation that rounds a right-hand side stores a bound and
writes the rounding into the row's slack (`setRhs`, which `translate` and `scaleRows` use), so a
rounded equality stays an equality. `anchorEqsInBox`, for unit-box coefficients, instead moves the
points onto the stored equalities, what that costs the inequalities written into their slacks.
`minkDiffOf`, `not` and the inner `reduceOverDomain` round downward instead, so the result stays
inside the exact one: a slack only widens a row, and cannot express that.

Enclosing on chosen directions: `plusOf`, `linCombOf`, `mtimesOf` and `intervalOf`, whose rows
nobody can predict from the inputs' — `ofBounds` is their shared shape and `DualBound` is where
a halfspace description certifies a direction for itself. `dualWeights` proposes the weights such
a certificate needs, by the exact simplex at ℚ; it is the driver, never a proof.
-/
