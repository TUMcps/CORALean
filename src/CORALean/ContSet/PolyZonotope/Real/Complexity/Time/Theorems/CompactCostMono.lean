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

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so a bound on the operand's size gives a
bound on the cost. -/
theorem PolyZonotope.compactCost_mono {h h' q q' : ℕ} (n p : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.compactCost n p h q ≤ PolyZonotope.compactCost n p h' q' := by
  cost_mono [PolyZonotope.compactCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
