module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpEvenCost`

Asserted, not proved, at `Vec ℝ n`: as `relaxExp`, with `ξ_E / 2` taken twice,
once off the center (`n` products, `n` subtractions) and once as the new
independent generator (`n` products), `ξ_E` itself evaluated twice as written,
and the two generators added (`n`).

The result is written once, and the result's `n * (d + q + 3) + p * (d + 1)` entries are written:
the center, the `d + 1`
dependent and `q + 1` independent generators, and the `d + 1` exponent columns.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpEven` costs at `Vec ℝ n` over `p` factors, keeping `d` dependent
generators with `q` independent ones, and `n * (d + q + 3) + p * (d + 1)` writes for the result. -/
def PolyZonotope.relaxExpEvenCost (n p d q : ℕ) : Cost :=
  ⟨4 * n + 2⟩ + (2 : ℕ) • PolyZonotope.relaxWidthCost + ⟨n * (d + q + 3) + p * (d + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
