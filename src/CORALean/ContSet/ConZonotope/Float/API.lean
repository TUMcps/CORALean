module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.ConZonotope.Float.Operations.API
public import CORALean.ContSet.ConZonotope.Float.Theorems.API
public import CORALean.ContSet.ConZonotope.Float.Instances

/-!
# Constrained zonotopes over a floating-point scalar, collected

Two roundings in two places: the centre and generators into the ambient error
box, the constraints into `P`, whose float form carries an interval right-hand
side. One box, not two.

`mtimes` keeps `P`, the constraints sitting on coefficients a linear map never sees, and its
rounding goes into the box by the float zonotope's argument. `intersection` is still missing: it
needs its agreement rows widened by `E₂ ⊖ E₁`, which is exactly what an interval right-hand
side is for — the two incoming boxes displace the point the rows pin together.
-/
