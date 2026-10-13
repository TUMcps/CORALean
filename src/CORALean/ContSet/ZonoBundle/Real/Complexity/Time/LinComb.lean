import CORALean.ContSet.ZonoBundle.Real.Operations.LinComb
import CORALean.ContSet.Zonotope.Real.Complexity.Time.LinComb

/-!
# `ZonoBundle.linCombCost`

Asserted, not proved: `Operations/LinComb.lean` runs `Zonotope.linComb` once
per pair of members, as `plus` does, and does nothing of its own.

`h₁` and `h₂` bound every member of the respective bundle rather than naming
one member's count, for the reason `mtimesCost` gives.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.linComb` costs at `Vec ℝ n` on bundles of `k₁` and `k₂`
members, none over `h₁` and `h₂` generators: one zonotope segment per pair. -/
def ZonoBundle.linCombCost (n k₁ k₂ h₁ h₂ : ℕ) : Cost :=
  (k₁ * k₂) • Zonotope.linCombCost n h₁ h₂

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
