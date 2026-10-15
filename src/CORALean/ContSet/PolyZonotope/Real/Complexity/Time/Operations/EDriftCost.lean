module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDiffCost

@[expose] public section

/-!
# `PolyZonotope.eDriftCost`

Asserted, not proved: `Operations/EDrift.lean` at `p` factors tests the parity of
`p - 1` exponents (a modulus and a comparison each, `2 * p`), then at most eight
further comparisons and parity tests choose the branch, and a branch returns at
most two `eDiff`s, which the definition writes out and so evaluates separately.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.eDrift` costs at `p` factors. -/
def PolyZonotope.eDriftCost (p : ℕ) : Cost := ⟨2 * p + 8⟩ + (2 : ℕ) • PolyZonotope.eDiffCost

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
