module

public import CORALean.ContSet.Capsule.Real.Operations.ConvHull
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.RadiusCost

@[expose] public section

/-!
# `Capsule.convHullCost`

Asserted, not proved: `Operations/ConvHull.lean` forms `c_ = (c + S.c) / 2`
(`2 * n`), `g_ = c - c_` (`n`), two `Capsule.radius` and their `max` (one).

The result is `c_`, `g_` and `r_`, `2 * n + 1` writes.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.convHull` costs at `Vec ℝ n`: the center, the generator, two radii and their
`max`, and `2 * n + 1` writes for the result's center, generator and radius. -/
def Capsule.convHullCost (n : ℕ) : Cost := ⟨3 * n + (2 * n + 1)⟩ + (2 : ℕ) • Capsule.radiusCost n +
⟨1⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
