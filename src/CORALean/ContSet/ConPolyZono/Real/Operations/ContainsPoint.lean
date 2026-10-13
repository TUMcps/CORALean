import CORALean.ContSet.ConPolyZono.Real.Operations.ExtPolyZonotope

/-!
# `ConPolyZono.containsPoint`

What `@conPolyZono/contains_` means to decide for a numeric operand `p`: the extended point `[p; 0]`
lies in the extended polynomial zonotope (`extPolyZonotope`), whose last coordinates are the
constraint residual `-b + A μ(α)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[p; 0]` lies in the extended polynomial zonotope. -/
def ConPolyZono.containsPoint (cPZ : ConPolyZono (Vec ℝ n)) (p : Vec ℝ n) : Prop :=
  (p, 0) ∈ cPZ.extPolyZonotope.construct


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
