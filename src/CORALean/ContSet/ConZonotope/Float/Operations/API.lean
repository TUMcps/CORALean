module

public import CORALean.ContSet.ConZonotope.Float.Operations.Isequal
public import CORALean.ContSet.ConZonotope.Float.Operations.Plus
public import CORALean.ContSet.ConZonotope.Float.Operations.LinCombGDiff
public import CORALean.ContSet.ConZonotope.Float.Operations.LinComb
public import CORALean.ContSet.ConZonotope.Float.Operations.Mtimes
public import CORALean.ContSet.ConZonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.ConZonotope.Float.Operations.Intersection
public import CORALean.ContSet.ConZonotope.Float.Operations.Split
public import CORALean.ContSet.ConZonotope.Float.Operations.Project
public import CORALean.ContSet.ConZonotope.Float.Operations.Reduce
public import CORALean.ContSet.ConZonotope.Float.Operations.LiftEq
public import CORALean.ContSet.ConZonotope.Float.Operations.ReduceLiftBy
public import CORALean.ContSet.ConZonotope.Float.Operations.ReduceLift
public import CORALean.ContSet.ConZonotope.Float.Operations.Empty
public import CORALean.ContSet.ConZonotope.Float.Operations.Origin
public import CORALean.ContSet.ConZonotope.Float.Operations.Reindex
public import CORALean.ContSet.ConZonotope.Float.Operations.NominalBoundWeights
public import CORALean.ContSet.ConZonotope.Float.Operations.BoundDotWeights
public import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
public import CORALean.ContSet.ConZonotope.Float.Operations.SeparatesAlong
public import CORALean.ContSet.ConZonotope.Float.Operations.IsDisjointLP
public import CORALean.ContSet.ConZonotope.Float.Operations.CartProd
public import CORALean.ContSet.ConZonotope.Float.Operations.MinkDiffV
public import CORALean.ContSet.ConZonotope.Float.Operations.ConIntersect
public import CORALean.ContSet.ConZonotope.Float.Operations.Rescale
public import CORALean.ContSet.ConZonotope.Float.Operations.Compact
public import CORALean.ContSet.ConZonotope.Float.Operations.IntersectStrip
public import CORALean.ContSet.ConZonotope.Float.Operations.Dependent
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilUp
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGDown
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGUp
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGDiff
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCDown
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCUp
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapDep
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.ConZonotope.Float.Operations.InteriorCert
public import CORALean.ContSet.ConZonotope.Float.Operations.InteriorMargin
public import CORALean.ContSet.ConZonotope.Float.Operations.RepresentsaEmptySet
public import CORALean.ContSet.ConZonotope.Float.Operations.CentreLo
public import CORALean.ContSet.ConZonotope.Float.Operations.CentreHi
public import CORALean.ContSet.ConZonotope.Float.Operations.IsFullDim
public import CORALean.ContSet.ConZonotope.Float.Operations.ContainsPoint
public import CORALean.ContSet.ConZonotope.Float.Operations.LinCombSameCentre
public import CORALean.ContSet.ConZonotope.Float.Operations.MtimesNominal
public import CORALean.ContSet.ConZonotope.Float.Operations.MtimesNominalErr
public import CORALean.ContSet.ConZonotope.Float.Operations.ZeroFeasible
public import CORALean.ContSet.ConZonotope.Float.Operations.CubMap

/-!
# What the float `ConZonotope` computes

`plus` keeps the constraints, padding each onto the wider coefficient space, and
rounds only the centre. `linComb` keeps them too, weighting each side's rows and
unit box by the interpolation parameter; halving is exact, so the only rounding
is the centre's and the centre generator's. `reduce` goes through the enclosing
zonotope and gives the constraints up, as it does over ℝ.

`mtimes` keeps the constraints, which sit on the coefficients, and pays the rounding of centre and
generators into the box as `Zonotope.mtimes` does. `intersection` copies both
operands' constraints and writes the agreement rows, whose right-hand side is the
one thing it computes: an interval holding every difference of the two nominal
points their error boxes allow, rounded outward.

`boundDot` bounds a direction by a dual certificate of the coefficient program,
weights from `HPolytope.dualWeights`, checked in rounded arithmetic with the unit
box paying for the residual: sound at every weight, an upper bound only.
`isDisjointLP` asks the same simplex for a separating direction and checks it with
two such bounds: `true` proves the sets disjoint, `false` decides nothing.
-/
