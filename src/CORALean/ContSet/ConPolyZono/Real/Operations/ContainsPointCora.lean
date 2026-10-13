import CORALean.ContSet.ConPolyZono.Real.Operations.ExtPolyZonotope

/-!
# `ConPolyZono.containsPointCora`

What CORA's source passes for a numeric operand: `S = [S; ones(m, size(S,2))]`, the extended point
`[p; 1]`, where the construction needs `[p; 0]` (`ConPolyZono.containsPoint`). Read from the source,
not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[p; ones(m)]` lies in the extended polynomial zonotope. -/
def ConPolyZono.containsPointCora (cPZ : ConPolyZono (Vec ℝ n)) (p : Vec ℝ n) : Prop :=
  (p, fun _ => 1) ∈ cPZ.extPolyZonotope.construct


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
