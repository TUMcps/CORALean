module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Real.Operations.Bilin
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin

@[expose] public section

/-!
# `Interval.quadMap`

CORA's `@interval/quadMap(I, Q)`: `quadMap(zonotope(I), Q)` boxed. The quadratic map
`x ↦ (xᵀQ₁x, …, xᵀQₘx)` over the box is bounded through the zonotope of the box and
`Zonotope.bilin`, then `Zonotope.interval`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.quadMap (Q : Fin m → Mat ℝ n n) (I : Interval (Vec ℝ n)) :
    Interval (Vec ℝ m) :=
  (Zonotope.bilin (PolyZonotope.quadBilin Q) I.zonotope I.zonotope).interval

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
