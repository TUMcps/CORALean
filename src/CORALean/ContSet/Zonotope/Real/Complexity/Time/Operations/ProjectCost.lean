module

public import CORALean.ContSet.Zonotope.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MapCost

@[expose] public section

/-!
# `Zonotope.projectCost`

Asserted, not proved: `Operations/Project.lean` is `Zonotope.map` of `LinearMap.funLeft`, which
reads coordinates `dims` out of a vector and computes nothing. Each of the `h + 1` columns is a
vector of `m` entries written, so one application costs `m` writes and the count is `mapCost` at
`m`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.project` costs onto `m` coordinates on `h` generators: `m` writes per column
of the center and generator matrix. -/
def Zonotope.projectCost (m h : ℕ) : Cost := Zonotope.mapCost ⟨m⟩ h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
