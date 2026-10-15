module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpEvenCost`

Asserted, not proved, at `Vec ℝ n`: as `relaxExp`, with `ξ_E / 2` taken twice,
once off the centre (`n` products, `n` subtractions) and once as the new
independent generator (`n` products), `ξ_E` itself evaluated twice as written,
and the two generators added (`n`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpEven` costs at `Vec ℝ n`. -/
def PolyZonotope.relaxExpEvenCost (n : ℕ) : Cost :=
  ⟨4 * n + 2⟩ + (2 : ℕ) • PolyZonotope.relaxWidthCost

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
