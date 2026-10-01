import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
import CORALean.ContSet.Ellipsoid.Real.Operations.Map
import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec
import CORALean.ContSet.Ellipsoid.Real.Operations.ApplyEqDotProduct
import CORALean.ContSet.Ellipsoid.Real.Operations.Pullback
import CORALean.ContSet.Ellipsoid.Real.Operations.ApplyMulVec
import CORALean.ContSet.Ellipsoid.Real.Operations.SupportBound
import CORALean.ContSet.Ellipsoid.Real.Operations.OfPoint
import CORALean.ContSet.Ellipsoid.Real.Operations.Project

/-!
# What an ellipsoid computes, collected

`mtimes` and the `map` it is, exact and the reason the generator form is stored;
`supportBound`, closed form in every direction; and `plus`, which encloses and
takes the parameter that enclosure needs. `Shape` is CORA's `Q`, read back off
the generators so the correspondence can be checked. `ofPoint` is the
degenerate case, `G` with no columns.
-/
