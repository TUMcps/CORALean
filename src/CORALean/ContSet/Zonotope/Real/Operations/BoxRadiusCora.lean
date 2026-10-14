module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor

@[expose] public section

/-!
# `Zonotope.boxRadiusCora`: `rad(interval(Z))`

The radius of the bounding box of a zonotope at coordinate `i`, `∑ⱼ |G j i|`, the `r` that
`@interval/zonotope.m` reads (`r = rad(I)`) when `split` boxes its operand.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `rad(interval(Z))` at coordinate `i`. -/
noncomputable def Zonotope.boxRadiusCora (Z : Zonotope (Vec ℝ n)) (i : Fin n) : ℝ :=
  ∑ j, |Z.G j i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
