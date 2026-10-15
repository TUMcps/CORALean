module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxDrift
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDriftCost

@[expose] public section

/-!
# `PolyZonotope.relaxDriftCost`

Asserted, not proved: `Operations/RelaxDrift.lean` is written with `eDrift`
appearing four times, so four evaluations are counted, no sharing being
assumed; then two subtractions-or-additions and two halvings.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxDrift` costs at `p` factors. -/
def PolyZonotope.relaxDriftCost (p : ℕ) : Cost := (4 : ℕ) • PolyZonotope.eDriftCost p + ⟨4⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
