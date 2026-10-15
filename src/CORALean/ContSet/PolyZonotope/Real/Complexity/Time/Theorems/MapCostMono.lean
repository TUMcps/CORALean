module

public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Map

@[expose] public section

/-!
# `PolyZonotope.mapCost_mono`

Monotone in the factor count and both generator counts, so bounds on the operand's sizes give
a bound on the cost.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the factor count and both generator counts, so bounds on the operand's sizes give
a bound on the cost. -/
theorem PolyZonotope.mapCost_mono {p p' h h' q q' : ℕ} (cf : Cost) (hp : p ≤ p') (hh : h ≤ h')
    (hq : q ≤ q') :
    PolyZonotope.mapCost cf p h q ≤ PolyZonotope.mapCost cf p' h' q' := by
  cost_mono [PolyZonotope.mapCost]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
