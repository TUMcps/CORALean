module

public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MapCost

@[expose] public section

/-!
# `Zonotope.projectCost`

Asserted, not proved: `Operations/Project.lean` is `Zonotope.map` of
`LinearMap.funLeft`, which reads coordinates `dims` out of a vector and
computes nothing, so one application is free and the count is `mapCost` at zero.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.project` costs on `h` generators: nothing, a coordinate read
per application. -/
def Zonotope.projectCost (h : ℕ) : Cost := Zonotope.mapCost 0 h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
