module

public import CORALean.ContSet.ConZonotope.Real.API
public import CORALean.ContSet.ConZonotope.Float.API

/-!
# Constrained zonotopes, both layers

The specification in `Real`, and in `Float` the refinement that splits its
rounding two ways: the centre and generators into an error box, the constraints
into the polytope's rows, an equality that must be rounded becoming a pair of inequalities.
-/
