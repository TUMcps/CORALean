module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.BilinCost

@[expose] public section

/-!
# `PolyZonotope.bilinCost_mono`

Monotone in the factor count and in both generator counts, so bounds on the
operands' sizes give a bound on the cost.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the factor count and in both generator counts, so bounds on the
operands' sizes give a bound on the cost. -/
theorem PolyZonotope.bilinCost_mono {p p' h₁ h₁' h₂ h₂' : ℕ} (cf : Cost)
    (hp : p ≤ p') (h1 : h₁ ≤ h₁') (h2 : h₂ ≤ h₂') :
    PolyZonotope.bilinCost cf p h₁ h₂ ≤ PolyZonotope.bilinCost cf p' h₁' h₂' :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.succ_le_succ h1) (Nat.succ_le_succ h2))
    (Nat.add_le_add_left hp _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
