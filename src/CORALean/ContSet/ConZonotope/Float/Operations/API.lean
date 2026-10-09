import CORALean.ContSet.ConZonotope.Float.Operations.Isequal
import CORALean.ContSet.ConZonotope.Float.Operations.Plus
import CORALean.ContSet.ConZonotope.Float.Operations.LinCombGDiff
import CORALean.ContSet.ConZonotope.Float.Operations.LinComb
import CORALean.ContSet.ConZonotope.Float.Operations.Mtimes
import CORALean.ContSet.ConZonotope.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.ConZonotope.Float.Operations.Intersection
import CORALean.ContSet.ConZonotope.Float.Operations.Split
import CORALean.ContSet.ConZonotope.Float.Operations.Project
import CORALean.ContSet.ConZonotope.Float.Operations.Reduce
import CORALean.ContSet.ConZonotope.Float.Operations.Empty
import CORALean.ContSet.ConZonotope.Float.Operations.Origin
import CORALean.ContSet.ConZonotope.Float.Operations.Reindex
import CORALean.ContSet.ConZonotope.Float.Operations.NominalBoundWeights
import CORALean.ContSet.ConZonotope.Float.Operations.BoundDotWeights
import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
import CORALean.ContSet.ConZonotope.Float.Operations.SeparatesAlong
import CORALean.ContSet.ConZonotope.Float.Operations.IsDisjointLP
import CORALean.ContSet.ConZonotope.Float.Operations.CartProd
import CORALean.ContSet.ConZonotope.Float.Operations.MinkDiffV
import CORALean.ContSet.ConZonotope.Float.Operations.ConIntersect
import CORALean.ContSet.ConZonotope.Float.Operations.Rescale
import CORALean.ContSet.ConZonotope.Float.Operations.Compact
import CORALean.ContSet.ConZonotope.Float.Operations.IntersectStrip
import CORALean.ContSet.ConZonotope.Float.Operations.Dependent
import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilUp
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGDown
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGUp
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGDiff
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCDown
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCUp
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapDep
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMap
import CORALean.ContSet.ConZonotope.Float.Operations.InteriorCert
import CORALean.ContSet.ConZonotope.Float.Operations.InteriorMargin
import CORALean.ContSet.ConZonotope.Float.Operations.RepresentsaEmptySet
import CORALean.ContSet.ConZonotope.Float.Operations.CentreLo
import CORALean.ContSet.ConZonotope.Float.Operations.CentreHi
import CORALean.ContSet.ConZonotope.Float.Operations.IsFullDim
import CORALean.ContSet.ConZonotope.Float.Operations.ContainsPoint

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
