module

public import CORALean.ContSet.HPolytope.Real.API
public import CORALean.ContSet.HPolytope.Float.API

/-!
# Polytopes by halfspaces, both layers

The specification in `Real`, and in `Float` the refinement that carries an error box, as every
float representation does, and keeps an equality it must round where a certificate pays the
rounding into that box, writing it as two inequalities otherwise.
-/
