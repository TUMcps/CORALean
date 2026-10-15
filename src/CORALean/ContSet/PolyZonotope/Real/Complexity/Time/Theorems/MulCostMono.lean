module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.BilinCostMono
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MulCost

@[expose] public section

/-!
# `PolyZonotope.mulCost_mono`

Monotone in both generator counts, so bounds on the operands' sizes give a
bound on the cost.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operands' sizes give a
bound on the cost. -/
theorem PolyZonotope.mulCost_mono {h₁ h₁' h₂ h₂' : ℕ} (n p : ℕ)
    (h1 : h₁ ≤ h₁') (h2 : h₂ ≤ h₂') :
    PolyZonotope.mulCost n p h₁ h₂ ≤ PolyZonotope.mulCost n p h₁' h₂' :=
  PolyZonotope.bilinCost_mono _ le_rfl h1 h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
