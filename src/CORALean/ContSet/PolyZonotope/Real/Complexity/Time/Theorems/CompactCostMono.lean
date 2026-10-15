module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.CompactCost

@[expose] public section

/-!
# `PolyZonotope.compactCost_mono`

Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem PolyZonotope.compactCost_mono {h h' : ℕ} (n p : ℕ) (hh : h ≤ h') :
    PolyZonotope.compactCost n p h ≤ PolyZonotope.compactCost n p h' :=
  Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul hh hh))
    (Nat.mul_le_mul_left _ hh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
